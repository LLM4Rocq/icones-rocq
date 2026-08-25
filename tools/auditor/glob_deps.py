"""Real Coq-level dependency edges, parsed from ``.glob`` files.

The graph's *doc-co-reference* edges (``tools.auditor.xref.build_entry_edges``)
connect entry ``A`` to entry ``B`` when ``A``'s statement / prose / snippet
**text** names an identifier ``B`` documents.  That misses dependencies the
docs describe narratively: a proof that *uses* a lemma without ever spelling
its backticked name in the surrounding prose.

Coq's ``.glob`` files (one per ``theories/**/*.v``, emitted by ``coqc
-emit-glob``) record every identifier *reference* with a byte range and every
top-level object's *definition*.  Parsing them yields a faithful
**statement-level** dependency relation: for a documented lemma ``L`` we
collect every identifier ``L``'s *statement* uses — references made only
inside a proof script (``Proof. … Qed.``) are masked out by byte position
(see :func:`proof_spans`) — then map those used identifiers back to the
entries that *document* them.  The result is the ``depends`` edge kind
(real Coq dependency), kept distinct from the ``mentions`` kind (doc
co-reference).

**Why statements only.**  The audit's question about an entry is *what it is
stated in terms of*, not how its proof happens to be scripted: a proof
routinely touches ten times as many documented entries as its statement
does, and drawing all of them buried the readable concept-level graph under
tactic-level noise (the owner's ruling, 2026-08).  A ``Definition`` body
that is a plain term (no ``Proof.`` script) still counts in full — for a
definition the body *is* the mathematical content, and those references are
what keep the machinery connected to the results stated in terms of it.

``.glob`` line grammar (the two forms we consume):

* **definition** — ``<kind> <bytestart>:<byteend> <modpath> <name>`` where
  ``<kind>`` is ``def``/``thm``/``lem``/``prf``/``abbrev``/``var``/``not``/…
  Top-level proof-bearing objects (``def``/``thm``/``lem``/``prf``) carry a
  ``<>`` modpath; section variables / local lets carry the *section* name.
* **reference** — ``R<bytestart>:<byteend> <modpath> <dotpath> <localname>
  <refkind>`` — a *use* of ``<modpath>.<localname>`` at that byte offset.

**Co-documented objects.** Two entries may legitimately document the *same*
Coq object — an overview entry and the object's own page, a paper theorem
and the "beyond the paper" entry that collects its engine.  When they do, a
reference *between* the objects they share says nothing about how the two
entries relate: ``wi_med`` referring to ``wi_obj`` is one internal step of
a single shared object set, yet it used to publish "Thm 4.19 is used by the
SAFT engine".

So exactly one class of edge is dropped: ``S -> T`` sourced from an object
that ``T`` *also documents* (:func:`build_claimant_map` supplies the
co-claimants).  Every other edge out of a co-documented object is kept —
it points at some third entry, and a dependency of a shared object is a
genuine dependency of **each** entry that documents it.  Suppressing those
too would delete hundreds of true edges to spare ten false ones.

The byte offsets inside a proof are *elaboration*-ordered, not source-ordered,
so a span cannot be delimited by "next larger offset".  Instead we walk the
file **line by line**: a definition line opens a region that owns every
subsequent reference line until the next definition line.  This matches how
coqdoc streams a ``.glob`` (declaration, then its references, then the next
declaration), and correctly attributes each ``R`` line to the object whose
body it belongs to.
"""

from __future__ import annotations

import re
from bisect import bisect_right
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

from .schema import ALL_TABS, Entry, ThreeTabDocument

#: An entry-to-entry dependency edge: ``((src_tab, src_id), (tgt_tab, tgt_id))``.
Edge = tuple[tuple[str, str], tuple[str, str]]

#: ``.glob`` definition line: ``<kind> <bs>:<be> <modpath> <name>``.  The name
#: may carry trailing tokens for notations; we keep only the first token.
_GLOB_DEF_RE = re.compile(
    r"^(def|thm|lem|prf|abbrev|var|not|constr|proj|scheme|rec|ind|sec|coind|inst)"
    r"\s+\d+:\d+\s+(\S+)\s+(\S.*)$"
)

#: ``.glob`` reference line:
#: ``R<bs>:<be> <modpath> <dotpath> <localname> <refkind>``.  The byte start
#: is captured so a reference can be located relative to the source file's
#: proof-script spans (statement-level masking).
_GLOB_REF_RE = re.compile(r"^R(\d+):\d+\s+(\S+)\s+\S+\s+(\S+)\s+(\S+)\s*$")

#: Reference kinds that name a *defined object* we may depend on (lemmas,
#: definitions, constructors, fields, instances).  Notations (``not``),
#: section variables (``var``), binders and library module markers are not
#: dependencies on documented entries.
_DEP_REF_KINDS = frozenset(
    {"def", "thm", "lem", "prf", "constr", "proj", "inst", "ind", "rec", "scheme"}
)

#: The tokens that matter to the proof-span scanner: comment delimiters,
#: string delimiters, the ``Proof`` vernacular opener and the four proof
#: terminators.  Word boundaries exclude identifiers like ``proof_of`` (Coq
#: identifiers may also contain ``'``, hence the primed classes).
_PROOF_EVENT_RE = re.compile(
    rb"\(\*|\*\)|\""
    rb"|(?<![A-Za-z0-9_'])(?:Proof|Qed|Defined|Admitted|Abort)(?![A-Za-z0-9_'])"
)


def proof_spans(src: bytes) -> list[tuple[int, int]]:
    """Byte spans ``[start, end)`` of the proof scripts in a ``.v`` source.

    A span opens at the ``Proof`` of a vernacular ``Proof.`` sentence and
    closes after the ``.`` of the next ``Qed`` / ``Defined`` / ``Admitted``
    / ``Abort``.  The scan is comment-aware (nested ``(* … *)``, where the
    words *Proof* and *Qed* occur freely as prose) and string-aware
    (``"…"`` with ``""`` escapes) so neither can open or close a span.

    Deliberate asymmetries, both erring toward *keeping* a reference:

    * a terminator with no open span is ignored — a tactic proof entered
      without ``Proof.`` (non-mathcomp style) is then simply not masked;
    * ``Proof`` NOT followed by ``.`` (``Proof using``, legacy ``Proof
      term``) opens nothing, for the same reason.

    An unterminated span runs to end-of-file (a truncated source mid-write;
    masking too much there is the safe direction, since the file is about
    to be re-read anyway).
    """
    spans: list[tuple[int, int]] = []
    depth = 0                # comment nesting
    open_at = -1             # start of the current proof span, -1 = none
    pos, n = 0, len(src)
    while pos < n:
        m = _PROOF_EVENT_RE.search(src, pos)
        if m is None:
            break
        tok, start, end = m.group(0), m.start(), m.end()
        if depth > 0:
            if tok == b"(*":
                depth += 1
            elif tok == b"*)":
                depth -= 1
            pos = end
            continue
        if tok == b"(*":
            depth = 1
            pos = end
            continue
        if tok == b"*)":     # stray close outside any comment: not ours
            pos = end
            continue
        if tok == b'"':      # skip the string literal ("" escapes a quote)
            i = end
            while True:
                j = src.find(b'"', i)
                if j == -1:
                    i = n
                    break
                if src[j + 1:j + 2] == b'"':
                    i = j + 2
                    continue
                i = j + 1
                break
            pos = i
            continue
        # A keyword, outside comments and strings.  Both the opener and the
        # terminators must be a full vernacular sentence: optional layout,
        # then the sentence-ending ``.``.
        j = end
        while j < n and src[j] in b" \t\r\n":
            j += 1
        is_sentence = src[j:j + 1] == b"."
        if tok == b"Proof":
            if open_at < 0 and is_sentence:
                open_at = start
                pos = j + 1
            else:
                pos = end
            continue
        if open_at >= 0 and is_sentence:
            spans.append((open_at, j + 1))
            open_at = -1
            pos = j + 1
        else:
            pos = end
    if open_at >= 0:
        spans.append((open_at, n))
    return spans


def parse_glob_uses(
    text: str,
    exclude_spans: list[tuple[int, int]] | None = None,
    stats: dict[str, int] | None = None,
) -> dict[str, set[str]]:
    """Parse one ``.glob`` file body into ``{object_name: {used_idents}}``.

    Walks ``text`` line by line.  A definition line opens the *current*
    region; every following reference line whose kind is a real object
    reference (see :data:`_DEP_REF_KINDS`) contributes its ``<localname>``
    to the current region's use-set.  Only the bare ``<localname>`` is kept
    (the last component of the dotted path) so it can be matched against an
    entry's ``rocq_idents``.  Self-references are *not* filtered here; the
    edge builder drops self-edges downstream.

    ``exclude_spans`` — the source file's :func:`proof_spans` — makes the
    result **statement-level**: a reference whose byte start falls inside a
    proof script is dropped.  ``None`` (no source available) keeps every
    reference, the historical statement-and-proof behaviour.

    ``stats``, when given, is a mutable tally: ``kept`` / ``masked`` are
    incremented per dependency-kind reference so the caller can report how
    much the statement mask removed.

    Multiple definition lines with the same name (re-opened sections,
    overloaded local lets) accumulate into one use-set — harmless, since we
    only query documented top-level names.
    """
    starts: list[int] = []
    ends: list[int] = []
    if exclude_spans:
        for s, e in sorted(exclude_spans):
            starts.append(s)
            ends.append(e)

    def in_proof(b: int) -> bool:
        i = bisect_right(starts, b) - 1
        return i >= 0 and b < ends[i]

    uses: dict[str, set[str]] = {}
    current: str | None = None
    for line in text.splitlines():
        m = _GLOB_DEF_RE.match(line)
        if m is not None:
            name = m.group(3).split()[0].strip()
            current = name
            uses.setdefault(current, set())
            continue
        r = _GLOB_REF_RE.match(line)
        if r is not None and current is not None:
            localname, refkind = r.group(3), r.group(4)
            if refkind in _DEP_REF_KINDS and localname != "<>":
                if starts and in_proof(int(r.group(1))):
                    if stats is not None:
                        stats["masked"] = stats.get("masked", 0) + 1
                    continue
                if stats is not None:
                    stats["kept"] = stats.get("kept", 0) + 1
                # Keep the bare local name (drop any dotted qualifier).
                uses[current].add(localname.rsplit(".", 1)[-1])
    return uses


def _glob_path_for(vfile_rel: str, theories_root: Path) -> Path | None:
    """Map a repo-relative ``theories/…/foo.v`` to its sibling ``.glob``.

    ``vfile_rel`` is the entry's ``rocq_files`` path (e.g.
    ``theories/programs/ex_reject_model.v``); the ``.glob`` sits next to the
    ``.v`` under ``theories_root``'s parent.  Returns ``None`` if the path is
    not under ``theories/`` or has no ``.v`` suffix.
    """
    rel = vfile_rel.strip()
    if not rel.endswith(".v"):
        return None
    base = theories_root.parent
    candidate = (base / rel).with_suffix(".glob")
    return candidate


def load_glob_uses(
    theories_root: str | Path,
    vfiles: Iterable[str],
    stats: dict[str, int] | None = None,
) -> tuple[dict[str, set[str]], list[str]]:
    """Load and merge ``{object_name: {used_idents}}`` for the given ``.v``s.

    ``vfiles`` is the set of repo-relative ``.v`` paths the documented
    entries reference (their ``rocq_files`` paths).  For each we read the
    sibling ``.glob`` and merge its per-object use-sets — **statement-level**:
    the ``.v`` source itself is read alongside to compute its proof-script
    spans (:func:`proof_spans`), and references made inside a proof are
    masked out.  An unreadable ``.v`` (but readable ``.glob``) degrades that
    one file to the unmasked statement-and-proof set rather than losing it.
    Returns ``(uses, missing)`` where ``missing`` is the list of ``.v``
    paths whose ``.glob`` was absent or unreadable — the caller turns a
    non-empty ``missing`` into a build NOTICE and degrades gracefully.
    ``stats`` (optional) tallies ``kept`` / ``masked`` reference counts
    across all files, for provenance reporting.

    A *single* unreadable file must never sink the build: a concurrent
    ``make`` truncates and rewrites ``.glob`` files in place, so one can
    legitimately be empty or half-written (and thus invalid UTF-8) while the
    other 60 are perfectly good.  Read errors, decode errors and parse
    errors are therefore all per-file: the offending path joins ``missing``
    and the walk continues.
    """
    theories_root = Path(theories_root)
    merged: dict[str, set[str]] = {}
    missing: list[str] = []
    for vfile in sorted(set(vfiles)):
        gpath = _glob_path_for(vfile, theories_root)
        if gpath is None:
            continue
        if not gpath.is_file():
            missing.append(vfile)
            continue
        spans: list[tuple[int, int]] | None
        try:
            spans = proof_spans(gpath.with_suffix(".v").read_bytes())
        except OSError:
            spans = None
        try:
            text = gpath.read_text(encoding="utf-8")
            parsed = parse_glob_uses(text, exclude_spans=spans, stats=stats)
        except (OSError, UnicodeDecodeError, ValueError):
            missing.append(vfile)
            continue
        if not parsed:
            # An empty or content-free .glob (a zero-byte file mid-rewrite)
            # carries no dependency information; count it as missing so the
            # provenance numbers describe what was actually read.
            missing.append(vfile)
            continue
        for name, used in parsed.items():
            if used:
                merged.setdefault(name, set()).update(used)
    return merged, missing


#: Owner key of a documented Coq object: ``(tab, entry_id)``.
OwnerKey = tuple[str, str]


def build_claimant_map(
    owners: Iterable[tuple[str, str, Entry]],
) -> dict[str, list[OwnerKey]]:
    """``{ident: [every entry documenting it]}``, in tab/document order.

    Note the plural: this map does **not** arbitrate a single owner.  An
    identifier listed by two entries is documented by two entries, and both
    of them really do depend on whatever that object's proof rests on — the
    only thing co-documentation makes meaningless is a "dependency" between
    the co-documenters themselves (see the module docstring, and
    :func:`build_glob_relation` for where the map is consulted).

    Deliberately *no* name filtering: unlike the text matcher, a ``.glob``
    object name is unambiguous, so short names (``eD``, ``lin``) and
    non-identifier cells stay eligible to source real dependencies.  Cells
    that name no Coq object simply never match a ``.glob`` region.

    Entries claiming an ident twice are recorded once, so the lists are
    genuine claimant sets and ``len(...) > 1`` means "co-documented".
    """
    claimants: dict[str, list[OwnerKey]] = {}
    for tab, eid, entry in owners:
        key = (tab, eid)
        for ident in entry.rocq_idents:
            claims = claimants.setdefault(ident, [])
            if key not in claims:
                claims.append(key)
    return claimants


@dataclass
class GlobRelation:
    """The ``.glob``-derived dependency relation plus its provenance.

    ``edges`` is the payload; every other field exists so the build can tell
    *silent degradation* apart from *a genuinely edgeless graph* — the
    distinction the strict guard in :func:`tools.auditor.render.render`
    turns into a hard failure instead of a quietly shipped, doc-only graph.

    * ``expected``  — glob data was asked for AND there is something to read
      (a ``theories`` root was supplied and the docs reference ``.v`` files).
      When ``expected`` holds but ``edges`` is empty, the build is broken,
      not empty.
    * ``n_vfiles`` / ``n_glob_found`` / ``n_glob_missing`` — how many of the
      documented ``.v`` sources had a sibling ``.glob``.
    * ``n_objects`` — Coq objects whose use-set was recovered from those
      ``.glob`` files (0 with files present ⇒ a parse-level regression).
    * ``notices``   — human-readable graceful-degradation lines.  These are
      NOT parser warnings and must never trip ``--strict``.
    """

    edges: list[Edge] = field(default_factory=list)
    notices: list[str] = field(default_factory=list)
    expected: bool = False
    n_vfiles: int = 0
    n_glob_found: int = 0
    n_glob_missing: int = 0
    n_objects: int = 0
    #: Statement-level accounting: dependency-kind references kept (in a
    #: statement or a plain definitional body) vs masked out as
    #: proof-script-only.  Both zero when no ``.glob`` was read.
    n_refs_stmt: int = 0
    n_refs_proof: int = 0
    #: ``{ident: [claimants]}`` for every ident more than one entry
    #: documents (see :func:`build_claimant_map`).  Docs hygiene, not a
    #: fault: co-documentation is legitimate and only costs the edges in
    #: ``suppressed``.
    contested: dict[str, list[OwnerKey]] = field(default_factory=dict)
    #: Edges dropped as *internal* cross-references — ``S -> T`` sourced
    #: from an object ``T`` also documents.  Sorted; excludes any pair that
    #: some other object independently justifies.
    suppressed: list[Edge] = field(default_factory=list)

    @property
    def available(self) -> bool:
        """True when at least one ``.glob`` file was actually read."""
        return self.n_glob_found > 0

    def summary(self) -> str:
        """One-line build-log summary of the glob resolution."""
        if not self.expected:
            return "glob deps: disabled (no theories root / no .v sources)"
        return (
            f"glob deps: {self.n_glob_found}/{self.n_vfiles} .v file(s) had a "
            f".glob · {self.n_objects} object(s) parsed · "
            f"{len(self.edges)} statement-level dependency edge(s) "
            f"({self.n_refs_stmt} refs kept, {self.n_refs_proof} "
            "proof-script refs masked)"
        )

    def report_lines(self, limit: int = 10) -> list[str]:
        """Build-log lines for the one edge class the pass drops, and why.

        Names every co-documented identifier and every edge suppressed as
        an internal cross-reference, so a reader of the log can check that
        the pass took away nothing else.  ``limit`` caps each list; the
        counts are always exact.
        """
        if not self.expected:
            return []
        lines = [
            "glob deps: co-documentation policy — an edge is dropped only "
            "when its TARGET also documents the object it was sourced from "
            "(an internal step inside one shared object set); every other "
            "edge out of a co-documented object is kept."
        ]
        if self.contested:
            lines.append(
                f"glob deps: {len(self.contested)} ident(s) documented by "
                "more than one entry (legitimate; each claimant keeps that "
                "object's real dependencies):"
            )
            for ident, keys in sorted(self.contested.items())[:limit]:
                who = ", ".join(f"{t}/{i}" for t, i in keys)
                lines.append(f"glob deps:   `{ident}` -> {who}")
            if len(self.contested) > limit:
                lines.append(
                    f"glob deps:   … and {len(self.contested) - limit} more"
                )
        if self.suppressed:
            lines.append(
                f"glob deps: {len(self.suppressed)} internal cross-reference"
                "(s) suppressed (co-documented endpoints):"
            )
            for (s_tab, s_id), (t_tab, t_id) in self.suppressed[:limit]:
                lines.append(
                    f"glob deps:   {s_tab}/{s_id} -> {t_tab}/{t_id}"
                )
            if len(self.suppressed) > limit:
                lines.append(
                    f"glob deps:   … and {len(self.suppressed) - limit} more"
                )
        return lines


def build_glob_relation(
    three: ThreeTabDocument,
    theories_root: str | Path | None,
) -> GlobRelation:
    """Statement-level Coq dependency edges ``A -> B`` from ``.glob`` files.

    For each documented entry ``A`` and each Coq object name ``A``
    documents, look up that object's ``.glob`` use-set (statement-level:
    proof-script references are masked, see :func:`proof_spans`), map every used
    identifier through the cross-tab documented-ident map
    (:func:`tools.auditor.xref.build_global_entry_map`) to the entry ``B``
    that *documents* it, and emit ``A -> B``.  Only edges to **other
    documented** entries are kept (this bounds the edge count: a proof uses
    hundreds of idents but only a handful are themselves documented nodes).
    Self-edges and duplicates are dropped; the list is sorted for
    determinism.

    One further exclusion, and only one: an edge sourced from an object
    ``B`` *also* documents is an internal step inside a shared object set
    rather than a relation between ``A`` and ``B`` — see the module
    docstring.  It is judged per sourcing object, so a co-documented
    object's dependencies on *third* entries survive; both the excluded
    edges and the co-documented names land in ``suppressed`` / ``contested``
    for :meth:`GlobRelation.report_lines`.

    ``theories_root=None`` yields an empty, ``expected=False`` relation with
    a NOTICE — the caller then renders a doc-co-reference-only graph.
    """
    if theories_root is None:
        return GlobRelation(
            notices=[
                "graph: no theories root provided; real Coq dependency edges "
                "(.glob) are disabled — doc co-reference edges only."
            ]
        )

    from .xref import build_global_entry_map

    entry_map = build_global_entry_map(three)

    # The (tab, id) set of real nodes + the entries to source edges from.
    known: set[tuple[str, str]] = set()
    owners: list[tuple[str, str, Entry]] = []
    vfiles: set[str] = set()
    for tab in ALL_TABS:
        doc = three.tab(tab)
        seen: set[int] = set()
        for section in _walk_sections(doc):
            for entry in section:
                if id(entry) in seen:
                    continue
                seen.add(id(entry))
                known.add((tab, entry.id))
                owners.append((tab, entry.id, entry))
                for rf in entry.rocq_files:
                    if rf.path:
                        vfiles.add(rf.path)

    # Only ``.v`` paths can have a sibling ``.glob``; anything else is not
    # part of the expected-vs-missing accounting.
    v_paths = {p for p in vfiles if p.strip().endswith(".v")}
    ref_stats: dict[str, int] = {}
    uses, missing = load_glob_uses(theories_root, vfiles, stats=ref_stats)

    notices: list[str] = []
    if not uses and missing:
        notices.append(
            "no .glob files found next to theories/ sources "
            f"({len(missing)} .v file(s) had no sibling .glob); "
            "real Coq dependency edges are unavailable — falling back to "
            "doc co-reference edges only. Build theories with "
            "`coqc -emit-glob` (the default) to enable them."
        )
    elif missing:
        notices.append(
            f"{len(missing)} .v file(s) had no sibling .glob; their real "
            "Coq dependencies are omitted (doc co-reference still covers them)."
        )

    # Every entry sources the use-set of every object it documents.  The
    # ONE exclusion is per (sourcing object, target) pair: an edge whose
    # target also documents the object it came from is an internal step
    # inside a shared object set, not a relation between the two entries
    # (see the module docstring).  Judging this per object rather than per
    # entry is what keeps a co-documented object's genuine dependencies —
    # on third entries — instead of discarding its whole use-set.
    claimants = build_claimant_map(owners)

    edges: set[Edge] = set()
    internal: set[Edge] = set()
    for tab, eid, entry in owners:
        src = (tab, eid)
        for name in entry.rocq_idents:
            co_documented = claimants.get(name, ())
            for ident in uses.get(name, ()):
                tgt = entry_map.get(ident)
                if tgt is None or tgt == src or tgt not in known:
                    continue
                if tgt in co_documented:
                    internal.add((src, tgt))
                else:
                    edges.add((src, tgt))

    return GlobRelation(
        edges=sorted(edges),
        notices=notices,
        expected=bool(v_paths),
        n_vfiles=len(v_paths),
        n_glob_found=max(0, len(v_paths) - len(missing)),
        n_glob_missing=len(missing),
        n_objects=len(uses),
        n_refs_stmt=ref_stats.get("kept", 0),
        n_refs_proof=ref_stats.get("masked", 0),
        contested={i: k for i, k in claimants.items() if len(k) > 1},
        # A pair some OTHER documented object independently justifies is a
        # real dependency, however it also arose; only report what the
        # exclusion actually cost.
        suppressed=sorted(internal - edges),
    )


def build_glob_edges(
    three: ThreeTabDocument,
    theories_root: str | Path,
) -> tuple[list[Edge], list[str]]:
    """``(edges, notices)`` view of :func:`build_glob_relation`.

    Kept as the stable two-tuple API used by the graph tests and any
    external caller; new code should prefer :func:`build_glob_relation`,
    whose result also carries the provenance the strict guard needs.
    """
    rel = build_glob_relation(three, theories_root)
    return rel.edges, rel.notices


def _walk_sections(doc) -> Iterable[list[Entry]]:
    """Yield each section's entry list (sections, chapters, beyond)."""
    for section in doc.sections:
        yield section.entries
    for chapter in doc.chapters:
        for section in chapter.sections:
            yield section.entries
    for contrib in doc.beyond:
        yield contrib.entries


__all__ = [
    "Edge",
    "GlobRelation",
    "OwnerKey",
    "build_claimant_map",
    "proof_spans",
    "parse_glob_uses",
    "load_glob_uses",
    "build_glob_relation",
    "build_glob_edges",
]
