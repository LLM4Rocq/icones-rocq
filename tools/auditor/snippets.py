"""Live Rocq snippets — resolve a card's code from ``theories/**/*.v``.

The auditor's cards historically carried *pasted* fenced ``coq`` blocks
(see ``docs/AUDITOR_FORMAT.md``).  Pasted text rots: the moment a lemma is
renamed, generalised or reordered, the dashboard shows a statement that no
longer exists in the sources it claims to audit — and nothing detects it.

This module makes the code blocks **live**.  Given a fenced block, it

1. splits the block into *declaration units* (``Definition …``,
   ``Lemma …``, ``HB.mixin Record …``, ``Notation "…" := …``, a quoted
   ``| Cn …`` case of an inductive, ``HB.instance Definition _ := …``)
   and the editorial material between them (blank lines, ``(* … *)``
   glosses, ``Section``/``End`` markers, ``Proof.``/``Qed.``);
2. looks every unit up **by identifier** in the on-disk ``.v`` sources —
   by notation string for a ``Notation``, by constructor name for a
   quoted case, by applied ``X.Build`` for an anonymous HB instance;
3. splices the *extracted source statement* back in place of the pasted
   text, recording the file and 1-based line it came from — **unless** the
   splice guard (:func:`_splice_verdict`) judges the statement not to be a
   plausible stand-in for the paste, in which case the paste is kept and
   the divergence reported.  Resolution locates a declaration; it does not
   license throwing curated content away.

The rewrite is a fixpoint: re-resolving an already-resolved block yields
the same text and reports no staleness, so pasting a rendered snippet
back into the Markdown is a valid way to silence a stale warning.

Unresolvable units keep their pasted text (so the build never loses
content) and are reported, which turns the build log into a staleness
dashboard: ``resolved`` / ``fallback`` / ``stale`` counts plus the exact
identifier that could not be found.

Resolution order for the declaration index of one ``.v`` file:

* a **regex scan** of the source text (always available — this is the path
  CI takes, since ``.glob`` files are build artefacts and are gitignored);
* a **``.glob`` overlay** when the sibling ``.glob`` exists (a local build,
  or a CI job that compiles the theories first).  ``.glob`` ``def``-style
  lines carry byte offsets of the declared name, which we convert to line
  numbers and back-scan to the opening keyword.  The overlay only *adds*
  names the regex scan missed, so behaviour degrades gracefully to the
  regex path when no ``.glob`` is present.

Statement extent: a declaration runs from its keyword (including any
immediately preceding ``#[…]`` attribute lines) to the first
statement-terminating ``.`` at bracket/comment/string depth 0 — i.e. the
``.`` before ``Proof.`` for proof-carrying objects, and the ``.`` closing
the ``:= …`` body for definitions, records and inductives (whose body *is*
the statement).  Long definition bodies are elided at the ``:=`` when they
exceed :data:`MAX_BODY_LINES`, so a card never turns into a page-long term.
"""

from __future__ import annotations

import os
import re
from dataclasses import dataclass, field
from pathlib import Path

__all__ = [
    "SourceDecl",
    "ResolvedUnit",
    "ResolvedBlock",
    "SnippetResolver",
    "SnippetStats",
    "clear_index_cache",
    "MAX_BODY_LINES",
    "MIN_SHRINK_LINES",
    "SHRINK_RATIO",
    "MIN_GROWTH_LINES",
    "GROWTH_RATIO",
]


# -- declaration grammar ----------------------------------------------------

#: Top-level keywords that open a declaration we can resolve by name.
#: Ordered longest-first where prefixes overlap (``HB.mixin Record`` before
#: ``Record``) so the alternation matches the longest form.
_KEYWORDS: tuple[str, ...] = (
    "HB.mixin Record",
    "HB.structure Definition",
    "HB.instance Definition",
    "HB.factory Record",
    "HB.builders Context",
    "Definition",
    "Theorem",
    "Lemma",
    "Corollary",
    "Proposition",
    "Remark",
    "Fact",
    "Property",
    "Example",
    "Fixpoint",
    "CoFixpoint",
    "Inductive",
    "CoInductive",
    "Variant",
    "Record",
    "Structure",
    "Class",
    "Instance",
    "Canonical",
    "Coercion",
    "Notation",
    "Reserved Notation",
    "Axiom",
    "Parameter",
    "Variable",
    "Hypothesis",
)

#: Modifiers that may prefix a declaration keyword.
_MODIFIERS = r"(?:Local|Global|Export|Program|#\[[^\]]*\]\s*)*"

_KW_ALT = "|".join(re.escape(k).replace(r"\ ", r"\s+") for k in _KEYWORDS)

#: ``[modifiers] <keyword> <name>`` — the name is a bare identifier.
_DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?P<mods>" + _MODIFIERS + r")"
    r"(?P<kw>" + _KW_ALT + r")\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
)

#: ``Notation "…" := …`` — resolved by its *notation string*, not a name.
_NOTATION_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?P<mods>" + _MODIFIERS + r")"
    r"(?P<kw>Reserved\s+Notation|Notation)\s+"
    r'"(?P<nota>(?:[^"\\]|\\.)*)"'
)

#: A declaration keyword alone on its line (the name follows on the next
#: one).  The regex scan cannot key such a declaration — the ``.glob``
#: overlay back-scans to it from the name's byte offset.
_DECL_OPEN_RE = re.compile(
    r"^[ \t]*(?:" + _MODIFIERS + r")(?P<kw>" + _KW_ALT + r")\s*$"
)

#: Anonymous HB instance: ``HB.instance Definition _ := …``.
_ANON_HB_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?P<mods>" + _MODIFIERS + r")"
    r"(?P<kw>HB\.instance\s+Definition)\s+_\b"
)

#: An attribute line that belongs to the declaration that follows it.
_ATTR_RE = re.compile(r"^[ \t]*#\[")

#: Keywords opening an inductive family whose body lists ``| Cn …`` cases.
_IND_KEYWORDS = ("Inductive", "CoInductive", "Variant")

#: A constructor case inside an inductive body — and, at the top level of a
#: fenced block, a *fragment* quoting one case of an inductive declared
#: elsewhere (``docs/PPL.md`` quotes single ``named_expr`` constructors).
_CTOR_RE = re.compile(r"^[ \t]*\|\s*(?P<name>[A-Za-z_][A-Za-z0-9_']*)")

#: Longest ``:= body`` (in lines) kept verbatim on a term-level definition
#: before the body is elided.  Records / inductives / structures are never
#: elided — their body is the statement.
MAX_BODY_LINES = 40

#: Splice sanity band.  Resolution proves *where* a declaration lives; it
#: does not prove that the extracted statement is a fair stand-in for what
#: the author pasted.  Two failure modes are real (both observed on the live
#: corpus) and both destroy curated content on the deployed page:
#:
#: * **shrink** — the source is written in proof mode (``Fixpoint f … : T.``
#:   followed by ``Proof. refine (…)``), so ``_statement_extent`` correctly
#:   stops at the signature, and a 48-line pasted interpreter collapses to
#:   its two-line type;
#: * **growth** — the paste is a deliberate *excerpt* of a large record or
#:   inductive (whose body is the statement and is therefore never elided),
#:   and the splice replaces a curated 32-line quote with a 178-line dump.
#:
#: When either trips, the paste is kept and the divergence is reported.  A
#: splice must only ever make a card *more* accurate, never less complete.
MIN_SHRINK_LINES = 6
SHRINK_RATIO = 0.6
MIN_GROWTH_LINES = 20
GROWTH_RATIO = 2.2

#: Keywords whose ``:= …`` body IS the statement (never elided).
_BODY_IS_STATEMENT = frozenset(
    {
        "HB.mixin Record",
        "HB.structure Definition",
        "HB.factory Record",
        "HB.builders Context",
        "Record",
        "Structure",
        "Class",
        "Inductive",
        "CoInductive",
        "Variant",
        "Notation",
        "Reserved Notation",
    }
)


# -- statement scanner ------------------------------------------------------


def _norm_kw(kw: str) -> str:
    """Collapse inner whitespace in a matched keyword (``HB.mixin  Record``)."""
    return re.sub(r"\s+", " ", kw.strip())


@dataclass
class _ScanState:
    """Bracket / comment / string depth carried across lines."""

    depth: int = 0  # (), {}, []
    comment: int = 0  # (* … *) nesting
    in_string: bool = False


def _scan_line(text: str, st: _ScanState) -> tuple[int | None, int | None]:
    """Advance ``st`` across ``text``; return ``(end_col, assign_col)``.

    ``end_col`` is the column just past the statement-terminating ``.``
    (depth 0, followed by whitespace / end of line), or ``None`` if the
    statement continues.  ``assign_col`` is the column of the first depth-0
    ``:=`` seen on this line, or ``None``.  Scanning stops at ``end_col``.
    """
    assign: int | None = None
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if st.comment:
            if ch == "*" and nxt == ")":
                st.comment -= 1
                i += 2
                continue
            if ch == "(" and nxt == "*":
                st.comment += 1
                i += 2
                continue
            i += 1
            continue
        if st.in_string:
            if ch == '"':
                # ``""`` is an escaped quote inside a Rocq string.
                if nxt == '"':
                    i += 2
                    continue
                st.in_string = False
            i += 1
            continue
        if ch == "(" and nxt == "*":
            st.comment += 1
            i += 2
            continue
        if ch == '"':
            st.in_string = True
            i += 1
            continue
        if ch in "([{":
            st.depth += 1
            i += 1
            continue
        if ch in ")]}":
            st.depth = max(0, st.depth - 1)
            i += 1
            continue
        if ch == ":" and nxt == "=" and st.depth == 0 and assign is None:
            assign = i
            i += 2
            continue
        if ch == ".":
            prev = text[i - 1] if i else ""
            after_ok = nxt in ("", " ", "\t")
            if st.depth == 0 and after_ok and prev != "." and prev != "(":
                return i + 1, assign
            i += 1
            continue
        i += 1
    return None, assign


def _last_code_line(chunk: list[str]) -> int:
    """Index of the last line of ``chunk`` carrying code outside a comment.

    Used to trim the trailing ``(* … *)`` block that documents the *next*
    inductive case off the previous one, both when indexing the sources and
    when consuming a quoted fragment (so the doc's own elision comments are
    preserved verbatim instead of being swallowed by the case above them).
    """
    depth = 0
    last = -1
    for i, line in enumerate(chunk):
        has_code = False
        j = 0
        while j < len(line):
            if line.startswith("(*", j):
                depth += 1
                j += 2
                continue
            if line.startswith("*)", j) and depth:
                depth -= 1
                j += 2
                continue
            if depth == 0 and not line[j].isspace():
                has_code = True
            j += 1
        if has_code:
            last = i
    return last


def _statement_extent(
    lines: list[str], start: int
) -> tuple[int, int | None]:
    """Return ``(end_index, assign_index)`` for the statement at ``lines[start]``.

    ``end_index`` is the index of the last line of the statement (inclusive);
    when no terminator is found the last line of ``lines`` is returned (the
    caller treats that as an elided / truncated block).  ``assign_index`` is
    the index of the line carrying the first depth-0 ``:=``, or ``None``.
    """
    st = _ScanState()
    assign_line: int | None = None
    for idx in range(start, len(lines)):
        end_col, assign = _scan_line(lines[idx], st)
        if assign is not None and assign_line is None:
            assign_line = idx
        if end_col is not None:
            return idx, assign_line
    return len(lines) - 1, assign_line


# -- source declarations ----------------------------------------------------


@dataclass(frozen=True)
class SourceDecl:
    """One declaration located in a ``.v`` source file."""

    name: str
    keyword: str
    vfile: str  # repo-relative, e.g. "theories/cones/precone.v"
    start_line: int  # 1-based, first line of the declaration
    end_line: int  # 1-based, last line of the extracted statement
    text: str  # the extracted statement, verbatim source formatting

    @property
    def line_count(self) -> int:
        return self.text.count("\n") + (0 if self.text.endswith("\n") else 1)


def _normalise_code(text: str) -> str:
    """Whitespace- and comment-insensitive normal form used for comparison."""
    # Drop (possibly nested) comments the cheap way, then collapse space.
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
            continue
        if text.startswith("*)", i) and depth:
            depth -= 1
            i += 2
            continue
        if not depth:
            out.append(text[i])
        i += 1
    return re.sub(r"\s+", " ", "".join(out)).strip()


def _normalise_notation(nota: str) -> str:
    """Normal form of a notation string (whitespace-insensitive)."""
    return re.sub(r"\s+", " ", nota).strip()


class _FileIndex:
    """Declaration index of a single ``.v`` file."""

    def __init__(self, vfile: str, text: str) -> None:
        self.vfile = vfile
        self.lines = text.splitlines()
        self.by_name: dict[str, SourceDecl] = {}
        self.by_notation: dict[str, SourceDecl] = {}
        self.by_constructor: dict[str, SourceDecl] = {}
        self.anonymous: list[SourceDecl] = []
        self._scan()

    # -- extraction ----------------------------------------------------

    def extract(self, start_idx: int, keyword: str) -> tuple[str, int, int]:
        """Extract the statement starting at ``lines[start_idx]``.

        Returns ``(text, start_line, end_line)`` — both 1-based.  Any
        contiguous ``#[…]`` attribute lines directly above are included.
        """
        first = start_idx
        while first > 0 and _ATTR_RE.match(self.lines[first - 1]):
            first -= 1
        end_idx, assign_idx = _statement_extent(self.lines, start_idx)
        body_lines = end_idx - (assign_idx if assign_idx is not None else end_idx)
        if (
            assign_idx is not None
            and keyword not in _BODY_IS_STATEMENT
            and body_lines > MAX_BODY_LINES
        ):
            # Elide an over-long term body at its ``:=``.
            kept = self.lines[first : assign_idx + 1]
            head = kept[:-1] + [_cut_at_assign(kept[-1]) + " (* … *)"]
            return "\n".join(head), first + 1, assign_idx + 1
        return "\n".join(self.lines[first : end_idx + 1]), first + 1, end_idx + 1

    def _add(self, decl: SourceDecl) -> None:
        # First definition of a name wins (a later ``Local`` shadow or a
        # re-export must not displace the primary declaration) — except that
        # a real declaration always outranks a section binder of the same
        # name (``Variable P`` must not hide ``Definition P``).
        old = self.by_name.get(decl.name)
        if old is None or (
            _decl_rank(decl.keyword) < _decl_rank(old.keyword)
        ):
            self.by_name[decl.name] = decl

    # -- scanning ------------------------------------------------------

    def _scan(self) -> None:
        idx = 0
        n = len(self.lines)
        while idx < n:
            line = self.lines[idx]
            handled = False
            m_nota = _NOTATION_RE.match(line)
            if m_nota is not None:
                kw = _norm_kw(m_nota.group("kw"))
                text, s, e = self.extract(idx, kw)
                decl = SourceDecl(
                    name=f'"{m_nota.group("nota")}"',
                    keyword=kw,
                    vfile=self.vfile,
                    start_line=s,
                    end_line=e,
                    text=text,
                )
                self.by_notation.setdefault(
                    _normalise_notation(m_nota.group("nota")), decl
                )
                idx = max(idx + 1, e)
                handled = True
            if not handled:
                m_anon = _ANON_HB_RE.match(line)
                if m_anon is not None:
                    kw = _norm_kw(m_anon.group("kw"))
                    text, s, e = self.extract(idx, kw)
                    self.anonymous.append(
                        SourceDecl(
                            name="_",
                            keyword=kw,
                            vfile=self.vfile,
                            start_line=s,
                            end_line=e,
                            text=text,
                        )
                    )
                    idx = max(idx + 1, e)
                    handled = True
            if not handled:
                m = _DECL_RE.match(line)
                if m is not None:
                    kw = _norm_kw(m.group("kw"))
                    text, s, e = self.extract(idx, kw)
                    self._add(
                        SourceDecl(
                            name=m.group("name"),
                            keyword=kw,
                            vfile=self.vfile,
                            start_line=s,
                            end_line=e,
                            text=text,
                        )
                    )
                    if kw in _IND_KEYWORDS:
                        self._scan_constructors(idx, e - 1)
                    idx = max(idx + 1, e)
                    handled = True
            if not handled:
                idx += 1

    def _scan_constructors(self, open_idx: int, end_idx: int) -> None:
        """Index the ``| Cn …`` cases of the inductive body ``[open_idx, end_idx]``.

        A case runs from its ``|`` line to the line before the next ``|``
        line (or to the end of the family).  Only line-leading bars count,
        so the compact ``Inductive T := A | B.`` form is skipped — its cases
        are not quotable as standalone fragments anyway.
        """
        bars = [
            i
            for i in range(open_idx, end_idx + 1)
            if _CTOR_RE.match(self.lines[i]) is not None
        ]
        for pos, start in enumerate(bars):
            m = _CTOR_RE.match(self.lines[start])
            if m is None:  # pragma: no cover — filtered above
                continue
            stop = bars[pos + 1] - 1 if pos + 1 < len(bars) else end_idx
            body = self.lines[start : stop + 1]
            keep = _last_code_line(body)
            if keep < 0:
                continue
            body = body[: keep + 1]
            # The last case carries the family's terminating ``.``; a quoted
            # case reads better without it.
            body[-1] = re.sub(r"\.\s*$", "", body[-1])
            self.by_constructor.setdefault(
                m.group("name"),
                SourceDecl(
                    name=m.group("name"),
                    keyword="constructor",
                    vfile=self.vfile,
                    start_line=start + 1,
                    end_line=start + len(body),
                    text="\n".join(body),
                ),
            )

    # -- .glob overlay -------------------------------------------------

    def apply_glob(self, glob_text: str, raw_bytes: bytes) -> int:
        """Add declarations the regex scan missed, using ``.glob`` positions.

        ``.glob`` ``def``-style lines carry the byte offset of the declared
        name; we map it to a line, back-scan to the opening keyword and
        extract from there.  Returns the number of names added.

        A ``.glob`` and its ``.v`` are **independent inputs**: CI downloads
        the ``.glob`` tree as an artefact of another workflow, so it routinely
        describes a slightly older revision of the checked-out sources (and a
        local tree may hold a half-written ``.glob`` mid-rebuild).  Every
        offset is therefore treated as untrusted: entries pointing past the
        end of the file are skipped, and the offset→line map is clamped to a
        real line index.  A mismatch must degrade to the regex index, never
        raise.
        """
        added = 0
        last_line = len(self.lines) - 1
        if last_line < 0:
            return 0
        n_bytes = len(raw_bytes)
        # Byte offset -> line number, computed once via a prefix table.  Note
        # a file ending in ``\n`` contributes a final entry equal to
        # ``n_bytes``, one past the last line — hence the clamp in
        # ``line_of`` below.
        newline_offsets = [0]
        for i, b in enumerate(raw_bytes):
            if b == 0x0A:
                newline_offsets.append(i + 1)

        def line_of(offset: int) -> int:
            lo, hi = 0, len(newline_offsets) - 1
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if newline_offsets[mid] <= offset:
                    lo = mid
                else:
                    hi = mid - 1
            return min(lo, last_line)  # 0-based line index, always in range

        for gline in glob_text.splitlines():
            m = _GLOB_DEF_RE.match(gline)
            if m is None:
                continue
            kind, start_b, name = m.group(1), int(m.group(2)), m.group(5)
            if start_b >= n_bytes:
                # The .glob describes a longer .v than the one on disk: this
                # object no longer exists at that offset.  Skipping is the
                # only sound reading — clamping would key an unrelated
                # declaration to the name.
                continue
            # Notation ``def`` lines carry a whole grammar entry as "name";
            # keep the first token, which is the identifier for real objects.
            name = name.split()[0].strip()
            if kind not in _GLOB_DEF_KINDS or not name or name in self.by_name:
                continue
            if not re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", name):
                continue
            idx = line_of(start_b)
            opener = self._backscan_opener(idx)
            if opener is None:
                continue
            open_idx, kw = opener
            text, s, e = self.extract(open_idx, kw)
            # Accept the mapping only when the declaration really spells the
            # name.  ``.glob`` also records machine-generated objects (HB's
            # ``phant_Build`` / ``HB_unnamed_factory_7``, the ``_rect`` /
            # ``_ind`` schemes of an inductive) and section binders whose
            # back-scan lands on an unrelated command; keying those to a
            # declaration that never mentions them would let a snippet
            # resolve to the wrong source text.
            if not re.search(r"\b" + re.escape(name) + r"\b", text):
                continue
            self._add(
                SourceDecl(
                    name=name,
                    keyword=kw,
                    vfile=self.vfile,
                    start_line=s,
                    end_line=e,
                    text=text,
                )
            )
            added += 1
        return added

    def _backscan_opener(self, idx: int, window: int = 6) -> tuple[int, str] | None:
        """Find the declaration opener at or just above line index ``idx``."""
        for back in range(0, window + 1):
            j = idx - back
            if j < 0:
                break
            if j > len(self.lines) - 1:  # defensive: never index past the file
                continue
            m = _DECL_RE.match(self.lines[j])
            if m is not None:
                return j, _norm_kw(m.group("kw"))
            m_open = _DECL_OPEN_RE.match(self.lines[j])
            if m_open is not None:
                return j, _norm_kw(m_open.group("kw"))
        return None


#: ``.glob`` definition line: ``<kind> <bytestart>:<byteend> <modpath> <name>``.
_GLOB_DEF_RE = re.compile(r"^([a-z]+)\s+(\d+):(\d+)\s+(\S+)\s+(\S.*)$")

#: ``.glob`` definition kinds that name a real top-level object.
_GLOB_DEF_KINDS = frozenset(
    {"def", "thm", "lem", "prf", "ind", "rec", "coind", "inst", "abbrev", "scheme"}
)


#: Keywords that merely bind a section-local name; a real declaration of the
#: same name always wins over these.
_BINDER_KEYWORDS = frozenset({"Variable", "Hypothesis", "Parameter", "Axiom"})


def _decl_rank(keyword: str) -> int:
    """0 for a real declaration, 1 for a section binder (lower wins)."""
    return 1 if keyword in _BINDER_KEYWORDS else 0


#: ``<Mixin>.Build`` — the HB builder an anonymous instance applies.  Used as
#: the identity key when matching ``HB.instance Definition _ := …`` blocks.
_HB_BUILDER_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_']*)\.Build\b")


def _hb_builder(text: str) -> str | None:
    """The first ``X.Build`` applied in ``text`` (an anonymous instance key)."""
    m = _HB_BUILDER_RE.search(text)
    return m.group(1) if m is not None else None


def _has_assign(text: str) -> bool:
    """True when ``text``'s first statement carries a depth-0 ``:=`` body."""
    st = _ScanState()
    for line in text.splitlines():
        end_col, assign = _scan_line(line, st)
        if assign is not None:
            return True
        if end_col is not None:
            return False
    return False


def _code_line_count(text: str) -> int:
    """Lines of ``text`` that carry code outside a comment (blank lines out).

    Comparing *code* lines keeps the splice guard from firing on a paste
    that merely carries a long editorial gloss, or on a source statement
    padded with blank lines.
    """
    n = 0
    depth = 0
    for line in text.splitlines():
        has_code = False
        j = 0
        while j < len(line):
            if line.startswith("(*", j):
                depth += 1
                j += 2
                continue
            if line.startswith("*)", j) and depth:
                depth -= 1
                j += 2
                continue
            if depth == 0 and not line[j].isspace():
                has_code = True
            j += 1
        if has_code:
            n += 1
    return n


def _splice_verdict(pasted: str, decl: SourceDecl) -> str:
    """``""`` when ``decl.text`` may replace ``pasted``, else why it may not.

    See :data:`MIN_SHRINK_LINES` for the rationale.  The check is
    deliberately *shape*-based rather than content-based: we cannot know
    which of the two texts is right, only whether swapping them would throw
    material away.  When in doubt the paste wins, because the paste is what
    a human curated and the report names it for a human to fix.
    """
    if _normalise_code(pasted) == _normalise_code(decl.text):
        return ""  # identical modulo whitespace/comments — nothing to lose
    paste_n = _code_line_count(pasted)
    src_n = _code_line_count(decl.text)
    if paste_n <= 0 or src_n <= 0:
        return ""
    if src_n < paste_n:
        # The source is written in proof mode: its ``:= body`` lives in the
        # proof script, which the statement extent (correctly) excludes.
        # Splicing would drop the whole body off the card.
        if _has_assign(pasted) and not _has_assign(decl.text):
            return (
                f"source statement is proof-mode ({src_n} code line(s)) while "
                f"the paste carries a := body ({paste_n}); kept the paste"
            )
        if paste_n - src_n >= MIN_SHRINK_LINES and src_n < SHRINK_RATIO * paste_n:
            return (
                f"source statement is {src_n} code line(s) vs {paste_n} pasted "
                "— the splice would drop material; kept the paste"
            )
        return ""
    if src_n - paste_n >= MIN_GROWTH_LINES and src_n > GROWTH_RATIO * paste_n:
        return (
            f"source statement is {src_n} code line(s) vs {paste_n} pasted "
            "— the paste reads as a curated excerpt; kept the paste"
        )
    return ""


def _cut_at_assign(line: str) -> str:
    """Truncate ``line`` just after its first depth-0 ``:=``."""
    _, col = _scan_line(line, _ScanState())
    if col is None:
        return line.rstrip()
    return line[: col + 2].rstrip()


# -- resolved blocks --------------------------------------------------------


@dataclass
class ResolvedUnit:
    """One declaration unit of a fenced block, after resolution."""

    name: str
    keyword: str
    resolved: bool
    stale: bool = False
    decl: SourceDecl | None = None
    pasted_line_count: int = 0
    reason: str = ""  # why it did not resolve (empty when resolved)
    #: True when the source statement really replaced the pasted text.  A
    #: resolved-but-not-spliced unit is one the splice guard held back (see
    #: :func:`_splice_verdict`): we know where it lives, we keep the paste.
    spliced: bool = False
    #: Why the splice was refused (empty unless ``resolved and not spliced``).
    mismatch: str = ""


@dataclass
class ResolvedBlock:
    """The outcome of resolving one fenced ``coq`` block."""

    text: str  # the block text to render (spliced, or the original)
    units: list[ResolvedUnit] = field(default_factory=list)
    source_file: str = ""  # the .v the resolved units came from
    files: list[str] = field(default_factory=list)  # every .v touched
    start_line: int = 0  # 1-based line of the first resolved unit
    end_line: int = 0  # 1-based last line of the last resolved unit
    changed: bool = False  # text differs from the pasted original

    @property
    def n_units(self) -> int:
        return len(self.units)

    @property
    def n_resolved(self) -> int:
        return sum(1 for u in self.units if u.resolved)

    @property
    def n_stale(self) -> int:
        return sum(1 for u in self.units if u.stale)

    @property
    def n_mismatched(self) -> int:
        """Units the splice guard held back (resolved, paste kept verbatim)."""
        return sum(1 for u in self.units if u.resolved and not u.spliced)

    @property
    def fully_resolved(self) -> bool:
        return bool(self.units) and self.n_resolved == self.n_units


@dataclass
class SnippetStats:
    """Corpus-wide roll-up of one build's snippet resolution."""

    blocks: int = 0
    blocks_fully_resolved: int = 0
    blocks_partial: int = 0
    blocks_unresolved: int = 0
    units: int = 0
    units_resolved: int = 0
    units_stale: int = 0
    units_mismatched: int = 0
    #: ``(context, identifier, reason)`` for every unit that fell back.
    fallbacks: list[tuple[str, str, str]] = field(default_factory=list)
    #: ``(context, identifier, "vfile:line — why")`` for every unit whose
    #: source statement was found but REFUSED as a replacement by the splice
    #: guard: the card renders the pasted text, unchanged.
    mismatched: list[tuple[str, str, str]] = field(default_factory=list)
    #: ``(context, identifier, vfile:line)`` for every unit whose pasted
    #: text materially disagrees with the source.
    stale: list[tuple[str, str, str]] = field(default_factory=list)
    #: ``(context, pasted_provenance, resolved_files)`` for blocks whose
    #: ``(* theories/…v *)`` lead comment does not name the file the
    #: declarations actually live in.
    provenance: list[tuple[str, str, str]] = field(default_factory=list)
    #: ``(context, provenance)`` for blocks in which no declaration at all
    #: was recognised (a bare term, a proof fragment): nothing to resolve,
    #: so they render exactly as pasted.
    opaque: list[tuple[str, str]] = field(default_factory=list)

    def record(
        self, block: ResolvedBlock, context: str, *, pasted_file: str | None = None
    ) -> None:
        self.blocks += 1
        self.units += block.n_units
        self.units_resolved += block.n_resolved
        self.units_stale += block.n_stale
        self.units_mismatched += block.n_mismatched
        if block.n_units and block.n_resolved == block.n_units:
            self.blocks_fully_resolved += 1
        elif block.n_resolved:
            self.blocks_partial += 1
        else:
            self.blocks_unresolved += 1
            if not block.n_units:
                self.opaque.append((context, pasted_file or ""))
        for u in block.units:
            if not u.resolved:
                self.fallbacks.append((context, u.name, u.reason))
            elif not u.spliced and u.decl is not None:
                self.mismatched.append(
                    (
                        context,
                        u.name,
                        f"{u.decl.vfile}:{u.decl.start_line} — {u.mismatch}",
                    )
                )
            elif u.stale and u.decl is not None:
                where = f"{u.decl.vfile}:{u.decl.start_line}"
                if u.pasted_line_count != u.decl.line_count:
                    where += (
                        f" (paste {u.pasted_line_count} line(s) → "
                        f"source {u.decl.line_count})"
                    )
                self.stale.append((context, u.name, where))
        if pasted_file and block.files and pasted_file not in block.files:
            self.provenance.append((context, pasted_file, ", ".join(block.files)))

    def merge(self, other: "SnippetStats") -> "SnippetStats":
        """Fold ``other`` into ``self`` (per-tab stats → per-build stats)."""
        self.blocks += other.blocks
        self.blocks_fully_resolved += other.blocks_fully_resolved
        self.blocks_partial += other.blocks_partial
        self.blocks_unresolved += other.blocks_unresolved
        self.units += other.units
        self.units_resolved += other.units_resolved
        self.units_stale += other.units_stale
        self.units_mismatched += other.units_mismatched
        self.fallbacks.extend(other.fallbacks)
        self.mismatched.extend(other.mismatched)
        self.stale.extend(other.stale)
        self.provenance.extend(other.provenance)
        self.opaque.extend(other.opaque)
        return self

    @property
    def resolved_pct(self) -> float:
        return (100.0 * self.units_resolved / self.units) if self.units else 0.0

    def summary(self) -> str:
        return (
            f"blocks={self.blocks} "
            f"(full={self.blocks_fully_resolved} partial={self.blocks_partial} "
            f"none={self.blocks_unresolved}) "
            f"decls={self.units} resolved={self.units_resolved} "
            f"({self.resolved_pct:.0f}%) "
            f"fallback={self.units - self.units_resolved} "
            f"stale={self.units_stale} "
            f"paste-kept={self.units_mismatched}"
        )

    def report_lines(self, *, limit: int = 0) -> list[str]:
        """Human-readable detail lines: fallbacks, staleness, provenance.

        ``limit`` caps each list (0 = no cap).  This is the maintenance
        dashboard: every line names something a human should fix in
        ``docs/*.md`` or in the sources.
        """

        def _cap(items: list) -> list:
            return items if limit <= 0 else items[:limit]

        out: list[str] = []
        if self.fallbacks:
            out.append(
                f"{len(self.fallbacks)} snippet declaration(s) could NOT be "
                "resolved from theories/ (rendered from the pasted text):"
            )
            for ctx, ident, reason in _cap(self.fallbacks):
                out.append(f"    {ctx}: `{ident}` — {reason}")
            if limit and len(self.fallbacks) > limit:
                out.append(f"    … {len(self.fallbacks) - limit} more")
        if self.mismatched:
            out.append(
                f"{len(self.mismatched)} snippet declaration(s) were found in "
                "theories/ but the source statement was REFUSED as a "
                "replacement (the card renders the pasted text unchanged):"
            )
            for ctx, ident, why in _cap(self.mismatched):
                out.append(f"    {ctx}: `{ident}` at {why}")
            if limit and len(self.mismatched) > limit:
                out.append(f"    … {len(self.mismatched) - limit} more")
        if self.stale:
            out.append(
                f"{len(self.stale)} pasted snippet(s) DISAGREE with the source "
                "(the rendered text is the source; the paste is stale):"
            )
            for ctx, ident, where in _cap(self.stale):
                out.append(f"    {ctx}: `{ident}` differs from {where}")
            if limit and len(self.stale) > limit:
                out.append(f"    … {len(self.stale) - limit} more")
        if self.provenance:
            out.append(
                f"{len(self.provenance)} snippet(s) name a provenance file that "
                "does not hold their declarations:"
            )
            for ctx, pasted, actual in _cap(self.provenance):
                out.append(f"    {ctx}: (* {pasted} *) but resolved in {actual}")
            if limit and len(self.provenance) > limit:
                out.append(f"    … {len(self.provenance) - limit} more")
        if self.opaque:
            out.append(
                f"{len(self.opaque)} snippet(s) declare nothing resolvable "
                "(a bare term / proof fragment) and render as pasted:"
            )
            for ctx, pasted in _cap(self.opaque):
                out.append(f"    {ctx}: (* {pasted or 'no provenance comment'} *)")
            if limit and len(self.opaque) > limit:
                out.append(f"    … {len(self.opaque) - limit} more")
        return out


# -- the resolver -----------------------------------------------------------


#: Declaration indexes are immutable for the lifetime of a build, and a
#: three-tab build resolves against the same ``theories/`` tree three times
#: (once per tab).  Cache the scan, keyed by (theories_root, repo_root,
#: use_glob); each :class:`SnippetResolver` still owns its own
#: :class:`SnippetStats`, so per-build reporting stays exact.
_INDEX_CACHE: dict[
    tuple[str, str, bool],
    tuple[
        dict[str, "_FileIndex"],
        dict[str, list[SourceDecl]],
        dict[str, list[SourceDecl]],
        dict[str, list[SourceDecl]],
        int,
    ],
] = {}


def clear_index_cache() -> None:
    """Drop the cached ``.v`` declaration indexes (tests, dev-server reloads)."""
    _INDEX_CACHE.clear()


class SnippetResolver:
    """Resolve fenced ``coq`` blocks against the on-disk Rocq sources.

    ``theories_root`` is the directory holding the ``.v`` files;
    ``repo_root`` (default: its parent) is the base the emitted ``vfile``
    paths are relative to, so they line up with
    :meth:`~tools.auditor.coqdoc.CoqdocResolver.github_url`.

    The index is built eagerly on first use (78 files ≈ a few ms) and kept
    in memory for the whole build.  A resolver over a missing
    ``theories_root`` resolves nothing — every block then renders exactly
    as it was pasted, which is the pre-existing behaviour.
    """

    def __init__(
        self,
        theories_root: str | Path | None,
        *,
        repo_root: str | Path | None = None,
        use_glob: bool = True,
    ) -> None:
        self._root = Path(theories_root) if theories_root is not None else None
        self._base = (
            Path(repo_root)
            if repo_root is not None
            else (self._root.parent if self._root is not None else None)
        )
        self._use_glob = use_glob
        self._files: dict[str, _FileIndex] = {}
        self._by_name: dict[str, list[SourceDecl]] = {}
        self._by_notation: dict[str, list[SourceDecl]] = {}
        self._by_constructor: dict[str, list[SourceDecl]] = {}
        self._glob_files = 0
        self._loaded = False
        self.stats = SnippetStats()

    # -- index ---------------------------------------------------------

    @property
    def available(self) -> bool:
        """True when at least one ``.v`` source was indexed."""
        self._load()
        return bool(self._files)

    @property
    def n_glob_files(self) -> int:
        """How many ``.glob`` overlays were applied (0 in a CI docs build)."""
        self._load()
        return self._glob_files

    def _load(self) -> None:
        if self._loaded:
            return
        self._loaded = True
        if self._root is None or not self._root.is_dir():
            return
        base = self._base or self._root.parent
        key = (str(self._root.resolve()), str(Path(base).resolve()), self._use_glob)
        cached = _INDEX_CACHE.get(key)
        if cached is not None:
            (
                self._files,
                self._by_name,
                self._by_notation,
                self._by_constructor,
                self._glob_files,
            ) = cached
            return
        for vpath in sorted(self._root.rglob("*.v")):
            try:
                rel = vpath.relative_to(base).as_posix()
            except ValueError:
                rel = vpath.as_posix()
            try:
                raw = vpath.read_bytes()
                text = raw.decode("utf-8")
            except (OSError, UnicodeDecodeError):
                continue
            try:
                index = _FileIndex(rel, text)
            except Exception:  # noqa: BLE001 — never let one odd file break a build
                continue
            if self._use_glob:
                gpath = vpath.with_suffix(".glob")
                try:
                    if gpath.is_file():
                        if index.apply_glob(gpath.read_text(encoding="utf-8"), raw):
                            self._glob_files += 1
                except Exception:  # noqa: BLE001
                    # A .glob is an *untrusted*, independently-produced input
                    # (a CI artefact of another workflow, or a file being
                    # rewritten by a concurrent `make`).  Nothing it can say
                    # may break the docs build: the regex index already
                    # stands on its own, so any failure degrades to it.
                    pass
            self._files[rel] = index
            for name, decl in index.by_name.items():
                self._by_name.setdefault(name, []).append(decl)
            for nota, decl in index.by_notation.items():
                self._by_notation.setdefault(nota, []).append(decl)
            for ctor, decl in index.by_constructor.items():
                self._by_constructor.setdefault(ctor, []).append(decl)
        _INDEX_CACHE[key] = (
            self._files,
            self._by_name,
            self._by_notation,
            self._by_constructor,
            self._glob_files,
        )

    # -- lookup --------------------------------------------------------

    def lookup(self, name: str, vfile_hint: str | None = None) -> SourceDecl | None:
        """Find the declaration of ``name``, preferring ``vfile_hint``."""
        self._load()
        if vfile_hint:
            index = self._files.get(vfile_hint)
            if index is not None:
                hit = index.by_name.get(name)
                if hit is not None:
                    return hit
        candidates = self._by_name.get(name, [])
        if len(candidates) == 1:
            return candidates[0]
        return None

    def lookup_notation(
        self, nota: str, vfile_hint: str | None = None
    ) -> SourceDecl | None:
        """Find a ``Notation "…"`` declaration by its notation string."""
        self._load()
        key = _normalise_notation(nota)
        if vfile_hint:
            index = self._files.get(vfile_hint)
            if index is not None:
                hit = index.by_notation.get(key)
                if hit is not None:
                    return hit
        candidates = self._by_notation.get(key, [])
        if len(candidates) == 1:
            return candidates[0]
        return None

    def lookup_constructor(
        self, name: str, vfile_hint: str | None = None
    ) -> SourceDecl | None:
        """Find one ``| Cn …`` case of an inductive family by its name."""
        self._load()
        if vfile_hint:
            index = self._files.get(vfile_hint)
            if index is not None:
                hit = index.by_constructor.get(name)
                if hit is not None:
                    return hit
        candidates = self._by_constructor.get(name, [])
        if len(candidates) == 1:
            return candidates[0]
        return None

    def lookup_anonymous(
        self,
        pasted: str,
        vfile_hint: str | None,
        *,
        exclude: set[int] | None = None,
    ) -> SourceDecl | None:
        """Best-effort match for ``HB.instance Definition _ := …``.

        Anonymous instances have no name to key on.  The identity key we use
        is the HB *builder* the instance applies (``isMCone.Build``), which
        separates the several anonymous instances a file typically carries;
        ties on that key are broken by identifier overlap, and an ambiguous
        result (no clear winner) resolves to ``None`` rather than to a
        plausible-looking wrong declaration.  ``exclude`` holds the
        ``id()``s of declarations already spliced into the current block, so
        two anonymous units never collapse onto the same source object.
        """
        self._load()
        if not vfile_hint:
            return None
        index = self._files.get(vfile_hint)
        if index is None:
            return None
        exclude = exclude or set()
        builder = _hb_builder(pasted)
        want = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", pasted))
        scored: list[tuple[float, SourceDecl]] = []
        for decl in index.anonymous:
            if id(decl) in exclude:
                continue
            cand_builder = _hb_builder(decl.text)
            if builder is not None and cand_builder is not None:
                if builder != cand_builder:
                    continue
            elif builder is not None or cand_builder is not None:
                continue
            have = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", decl.text))
            if not want or not have:
                continue
            scored.append((len(want & have) / len(want | have), decl))
        if not scored:
            return None
        scored.sort(key=lambda t: t[0], reverse=True)
        best = scored[0]
        if best[0] < 0.4:
            return None
        if len(scored) > 1 and best[0] - scored[1][0] < 0.1:
            return None  # ambiguous — two equally plausible instances
        return best[1]

    # -- block resolution ----------------------------------------------

    def resolve_block(
        self, raw: str, source_file: str | None = None, *, context: str = ""
    ) -> ResolvedBlock:
        """Resolve one fenced ``coq`` block; splice in the source statements.

        ``source_file`` is the block's provenance path (the
        ``(* theories/foo.v *)`` lead comment the parser already extracts).
        Non-declaration lines — blank lines, ``(* … *)`` glosses,
        ``Section``/``End`` markers, ``Proof.``/``Qed.`` — are preserved
        verbatim, so the editorial shape of the block survives.
        """
        lines = raw.splitlines()
        self._load()
        block = ResolvedBlock(text=raw)
        if not self._files:
            # No sources indexed: pure pass-through (legacy behaviour).
            self.stats.record(block, context or "?", pasted_file=source_file)
            return block

        out: list[str] = []
        units: list[ResolvedUnit] = []
        starts: list[tuple[str, int]] = []
        ends: list[tuple[str, int]] = []
        used: set[int] = set()
        hint = source_file if source_file in self._files else None
        idx = 0
        n = len(lines)
        while idx < n:
            unit = _match_unit(lines, idx)
            if unit is None:
                out.append(lines[idx])
                idx += 1
                continue
            kind, kw, key, first_idx = unit
            if kind == "ctor":
                # A quoted inductive case has no terminating ``.`` of its
                # own, so its extent is bounded by the next unit opener (the
                # next ``|`` case or any declaration keyword) rather than by
                # the statement scanner, which would run on into whatever
                # the block quotes next.
                stmt_end, _ = _statement_extent(lines, idx)
                end_idx = stmt_end
                for j in range(idx + 1, min(stmt_end, n - 1) + 1):
                    if _match_unit(lines, j) is not None:
                        end_idx = j - 1
                        break
                keep = _last_code_line(lines[idx : end_idx + 1])
                if keep >= 0:
                    end_idx = idx + keep
            else:
                end_idx, _ = _statement_extent(lines, idx)
            pasted = "\n".join(lines[first_idx : end_idx + 1])
            # ``#[…]`` attribute lines above the keyword were already emitted
            # as plain lines; drop them so the unit is spliced in one piece.
            for _ in range(idx - first_idx):
                if out:
                    out.pop()
            decl: SourceDecl | None = None
            reason = ""
            if kind == "name":
                decl = self.lookup(key, hint)
                if decl is None:
                    reason = (
                        f"not found in {hint}"
                        if hint
                        else "not found (or ambiguous) in theories/"
                    )
            elif kind == "notation":
                decl = self.lookup_notation(key, hint)
                if decl is None:
                    reason = "notation string not found in " + (hint or "theories/")
            elif kind == "ctor":
                decl = self.lookup_constructor(key, hint)
                if decl is None:
                    # Not a constructor of any indexed inductive — most
                    # likely a ``match`` branch quoted out of context.  Leave
                    # the pasted lines alone and say nothing: this is not a
                    # declaration the entry claims to document.
                    out.extend(lines[first_idx : end_idx + 1])
                    idx = end_idx + 1
                    continue
            else:  # anonymous
                decl = self.lookup_anonymous(pasted, hint, exclude=used)
                if decl is None:
                    reason = "anonymous HB.instance — no confident source match"

            pasted_lc = pasted.count("\n") + 1
            if decl is None:
                out.extend(lines[first_idx : end_idx + 1])
                units.append(
                    ResolvedUnit(
                        name=key,
                        keyword=kw,
                        resolved=False,
                        pasted_line_count=pasted_lc,
                        reason=reason,
                    )
                )
            else:
                stale = _normalise_code(pasted) != _normalise_code(decl.text)
                # The splice guard has the last word: resolution located the
                # declaration, but the extracted statement is only allowed to
                # REPLACE the paste when it is a plausible stand-in for it.
                mismatch = _splice_verdict(pasted, decl)
                if mismatch:
                    out.extend(lines[first_idx : end_idx + 1])
                else:
                    out.extend(decl.text.splitlines())
                units.append(
                    ResolvedUnit(
                        name=key,
                        keyword=kw,
                        resolved=True,
                        stale=stale,
                        decl=decl,
                        pasted_line_count=pasted_lc,
                        spliced=not mismatch,
                        mismatch=mismatch,
                    )
                )
                # A held-back unit still contributes its *anchor* line (the
                # card's "source" link stays useful) but NOT an end line: the
                # rendered text is the paste, so it spans no source range.
                starts.append((decl.vfile, decl.start_line))
                if not mismatch:
                    ends.append((decl.vfile, decl.end_line))
                used.add(id(decl))
                if decl.vfile not in block.files:
                    block.files.append(decl.vfile)
                if not block.source_file:
                    block.source_file = decl.vfile
            idx = end_idx + 1

        text = "\n".join(out)
        if raw.endswith("\n"):
            text += "\n"
        block.units = units
        block.text = text if any(u.resolved for u in units) else raw
        block.changed = block.text != raw
        # The header line range describes the *primary* file only (a block
        # that quotes two files gets its range from the first one).
        primary = block.source_file
        prim_starts = [ln for vf, ln in starts if vf == primary]
        prim_ends = [ln for vf, ln in ends if vf == primary]
        block.start_line = min(prim_starts) if prim_starts else 0
        block.end_line = max(prim_ends) if prim_ends else 0
        self.stats.record(block, context or "?", pasted_file=source_file)
        return block


def _match_unit(
    lines: list[str], idx: int
) -> tuple[str, str, str, int] | None:
    """Classify ``lines[idx]`` as a declaration opener.

    Returns ``(kind, keyword, key, first_idx)`` where ``kind`` is
    ``"name"`` / ``"notation"`` / ``"anon"`` / ``"ctor"``, ``key`` is the
    identifier (the notation string for ``"notation"``, the constructor
    name for ``"ctor"``, ``"_"`` for ``"anon"``), and ``first_idx`` is the
    first line of the unit including preceding ``#[…]`` attribute lines.
    ``None`` when the line does not open a declaration.
    """
    line = lines[idx]
    first = idx
    while first > 0 and _ATTR_RE.match(lines[first - 1]):
        first -= 1
    m_nota = _NOTATION_RE.match(line)
    if m_nota is not None:
        return ("notation", _norm_kw(m_nota.group("kw")), m_nota.group("nota"), first)
    m_anon = _ANON_HB_RE.match(line)
    if m_anon is not None:
        return ("anon", _norm_kw(m_anon.group("kw")), "_", first)
    m = _DECL_RE.match(line)
    if m is not None:
        return ("name", _norm_kw(m.group("kw")), m.group("name"), first)
    m_ctor = _CTOR_RE.match(line)
    if m_ctor is not None:
        # Only reachable at block level: a ``|`` inside a declaration is
        # swallowed by that declaration's statement extent.  So this is a
        # fragment quoting one case of an inductive declared elsewhere.
        return ("ctor", "constructor", m_ctor.group("name"), first)
    return None


# -- check mode -------------------------------------------------------------


def _check_main(argv: list[str] | None = None) -> int:
    """``python -m tools.auditor.snippets`` — the live-snippet checker.

    Parses the three Markdown sources exactly as the dashboard build does
    (so the numbers agree with ``tools/build_auditor.py``) and prints the
    resolution report without rendering anything.  Exits 1 when a snippet
    declaration could not be resolved, or — with ``--strict`` — when any
    pasted block disagrees with the sources.
    """
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m tools.auditor.snippets",
        description=(
            "Resolve every fenced coq block of the auditor sources against "
            "theories/**/*.v and report unresolved / stale / mis-attributed "
            "snippets."
        ),
    )
    p.add_argument("--paper", default="docs/PAPER.md")
    p.add_argument("--ppl", default="docs/PPL.md")
    p.add_argument("--examples", default="docs/EXAMPLES.md")
    p.add_argument(
        "--project-root",
        default=".",
        help="Directory holding theories/ (default: the current directory)",
    )
    p.add_argument("--coqproject", default="_CoqProject")
    p.add_argument("--github-repo", default="LLM4Rocq/icones-rocq")
    p.add_argument("--commit", default="main")
    p.add_argument(
        "--strict",
        action="store_true",
        help="Also fail when a pasted block disagrees with the source.",
    )
    p.add_argument(
        "--annotate",
        action="store_true",
        default=None,
        help=(
            "Emit GitHub Actions ::warning:: annotations for every held-back "
            "splice (default: on when GITHUB_ACTIONS is set)."
        ),
    )
    args = p.parse_args(argv)
    annotate = (
        args.annotate
        if args.annotate is not None
        else bool(os.environ.get("GITHUB_ACTIONS"))
    )

    from .coqdoc import CoqdocResolver, parse_coqproject
    from .parser import parse_three_tabs, snippet_stats

    root = Path(args.project_root).resolve()
    resolver = CoqdocResolver(
        bindings=parse_coqproject(args.coqproject),
        github_repo=args.github_repo,
        commit=args.commit,
    )
    three, _ = parse_three_tabs(
        paper_path=args.paper,
        ppl_path=args.ppl,
        examples_path=args.examples,
        resolver=resolver,
        project_root=root,
        strict=False,
    )
    stats = snippet_stats(three)
    probe = SnippetResolver(root / "theories", repo_root=root)
    print(f"[snippets] sources: {root / 'theories'}")
    print(
        f"[snippets] .glob overlays applied: {probe.n_glob_files} "
        "(0 is normal — .glob files are build artefacts and are gitignored)"
    )
    print(f"[snippets] {stats.summary()}")
    for line in stats.report_lines():
        print(f"[snippets] {line}")
    if annotate:
        # This step is deliberately non-blocking (a stale paste must never
        # stop the Pages deploy), which used to mean nobody ever saw it.  An
        # annotation surfaces every held-back splice on the run summary of a
        # GREEN build, which is where a maintenance signal belongs.
        for ctx, ident, why in stats.mismatched:
            print(f"::warning title=live snippet::{ctx}: `{ident}` at {why}")
    unresolved = stats.units - stats.units_resolved
    if unresolved:
        print(f"[snippets] FAIL: {unresolved} declaration(s) unresolved")
        return 1
    if args.strict and stats.units_stale:
        print(f"[snippets] FAIL (--strict): {stats.units_stale} stale paste(s)")
        return 1
    print("[snippets] OK")
    return 0


if __name__ == "__main__":  # pragma: no cover
    import sys

    sys.exit(_check_main())
