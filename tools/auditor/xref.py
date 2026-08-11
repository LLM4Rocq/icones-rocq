"""Clickable identifier cross-references inside highlighted snippets.

Post-parse, pre-render pass: once a tab's :class:`~tools.auditor.schema.
Document` is fully assembled, build an ``{ident: entry_id}`` map from
every entry's ``rocq_idents`` (sections, chapters AND beyond trees) and
wrap matching identifier tokens in each snippet's Pygments HTML in
``<a class="code-xref" …>`` anchors pointing at the defining entry's
page.

Two passes cooperate
---------------------
* :func:`linkify_document` is the *per-tab* pass.  It links an ident to
  another entry **of the same tab** with a uniform ``../entries/<id>.html``
  href.  Single-tab callers (and the legacy goldens) rely on it.
* :func:`linkify_all` is the *global* pass run by the orchestrator once
  all three tabs are parsed.  It mops up the tokens the per-tab pass left
  plain by consulting (a) a cross-tab entry map — so a PPL snippet can
  link ``EM_term`` to its Paper entry page — and (b) a source-line index
  scraped from ``theories/**/*.v`` — so an ident documented *nowhere*
  links to its GitHub blob ``#L`` line.  Cross-tab entry hrefs are
  tab-aware (``../../<tab>/entries/<id>.html``); source hrefs are
  absolute and carry the extra ``code-xref-src`` class.

Both passes share the same token machinery, so they compose: the global
pass only ever sees tokens the per-tab pass left unwrapped (a span that
already holds an ``<a>`` can never re-match — see *Idempotency*).

Design decisions
----------------
* **Token classes** — Pygments' Coq/Rocq lexer emits plain names as
  ``<span class="n">ident</span>`` (verified on real project source:
  only ``Token.Name`` / class ``n`` occurs).  We also accept ``nf`` /
  ``nb`` / ``nc`` defensively; comment (``c``) and string (``s2``)
  spans are never touched.  Identifiers with underscores are single
  tokens (the lexer does not split on ``_``).
* **Minimum length** — idents shorter than :data:`MIN_IDENT_LEN` (4)
  are excluded: 1–3 char names (``f``, ``mu``, ``der``) are pervasive
  as local binders and would over-link.
* **Duplicates** — when two entries claim the same ident, the entry
  whose ``id`` equals ``slugify_label(ident)`` wins (it *is* the
  ident's page); otherwise first-wins in document order.  The global
  entry map applies the same rule across tabs, ordering the tabs
  deterministically (paper, then ppl, then examples).
* **Source ambiguity** — when an ident is declared at top level in more
  than one ``.v`` file the source index drops it entirely: a link to one
  of several definitions would be a *wrong* link, which is worse than no
  link.  Idents that resolve to a documented entry never consult the
  source index, so a name that is both documented and multiply-declared
  still links (to its entry page).
* **URL prefix** — every page that embeds snippet HTML lives at depth 2
  from the site root (``<tab>/sections/x.html``, ``<tab>/entries/x.html``,
  ``<tab>/beyond/x.html``).  A same-tab entry link is therefore
  ``../entries/<id>.html``; a cross-tab one is
  ``../../<tab>/entries/<id>.html``.
* **Self-links** — when linkifying a snippet owned by entry E,
  occurrences mapping back to E are left unwrapped (a self-link is
  noise on E's own page).
* **Idempotency** — the token regex matches ``[^<]+`` span bodies only;
  a span already containing an ``<a>`` can never match again, so
  running either pass twice (or both in sequence) is a no-op on the
  already-linked tokens.

Prose cross-references
----------------------
The same maps linkify prose: statement HTML, entry detail prose,
section/chapter intros and notes.  Prose is rendered by the parser's
``_inline_to_html`` into ``<code>ident</code>`` spans (never Pygments).
We wrap a ``<code>`` body in a ``code-xref`` anchor when, after
HTML-unescape, it ``fullmatch``es the identifier regex, is at least
:data:`MIN_IDENT_LEN` long and resolves to a target.  Math / notation
``<code>`` (spaces, operators, ``⟦``, ``∫``, ``·`` …) never matches the
identifier regex and is left untouched, as are self-links and unknown
idents.  The ``[^<]+`` body discipline keeps the pass idempotent.
"""

from __future__ import annotations

import html as html_mod
import re
from pathlib import Path
from typing import Callable, Iterable, Iterator

from .coqdoc import CoqdocResolver
from .schema import (
    ALL_TABS,
    CoqSnippet,
    CrossRef,
    Document,
    Entry,
    ThreeTabDocument,
)

#: Identifiers shorter than this are never linkified (over-link noise).
MIN_IDENT_LEN = 4

#: Cross-ref kinds of the *directional* relation shown as Uses / Used by.
#: They are dependency claims, so only the proof-level ``.glob`` relation
#: may fill them (``via='glob'``); see :func:`attach_glob_relations`.
_RELATION_KINDS = ("uses", "used-by")

#: Cross-ref kind of the *undirected* doc co-reference — "these two entries
#: are written about the same identifier".  Always ``via='doc'``, filed on
#: both endpoints, and never a dependency claim.
MENTION_KIND = "mentions"

#: Shape of a linkable Rocq identifier — plain name, no dots/operators.
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

#: A single Pygments name token.  ``[^<]+`` keeps the match within one
#: leaf span: spans that already contain markup (e.g. an ``<a>`` from a
#: previous pass) can never match, which makes the pass idempotent.
_NAME_SPAN_RE = re.compile(r'<span class="(n|nf|nb|nc)">([^<]+)</span>')

#: Relative href prefix from any snippet-embedding page (all depth 2 from
#: the site root: ``<tab>/<kind>/x.html``) back to its own tab root.
_HREF_PREFIX = "../"

#: A single ``<code>…</code>`` prose span.  ``[^<]+`` keeps the match
#: within one leaf span: a ``<code>`` already containing markup (e.g. an
#: ``<a>`` from a previous pass) can never match, keeping the pass
#: idempotent.
_CODE_SPAN_RE = re.compile(r"<code>([^<]+)</code>")

#: A ``code-xref`` anchor already emitted by a previous linkify pass.  The
#: captured body is the (escaped) identifier that anchor links.  Used to
#: pre-seed the per-block "already linked" set so the first-occurrence-only
#: policy stays stable when the per-tab and global passes run in sequence:
#: an ident wrapped by the first pass is recognised as already-linked by
#: the second, whose later plain occurrences are then left untouched.
_LINKED_XREF_RE = re.compile(r'<a class="code-xref[^"]*"[^>]*>([^<]+)</a>')

#: Top-level Rocq declaration keywords whose first ``\w+`` token names a
#: definition.  ``Notation`` is handled by the same pattern but only its
#: bare-identifier form matches (a quoted ``Notation "…"`` name fails the
#: identifier class and is skipped).
_DECL_KEYWORDS = (
    "Definition",
    "Lemma",
    "Theorem",
    "Corollary",
    "Proposition",
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
    "Notation",
)

#: ``<keyword> <name>`` at the start of a (possibly indented) line.  The
#: name is captured as a bare identifier; ``Notation "…"`` forms whose
#: name is a string literal simply fail this pattern (the ``"`` is not in
#: the identifier class) and are skipped.
_DECL_RE = re.compile(
    r"^\s*(?:" + "|".join(_DECL_KEYWORDS) + r")\s+([A-Za-z_][A-Za-z0-9_']*)"
)

#: Named ``HB.instance``/``HB.structure`` definitions of the form
#: ``HB.instance Definition Name := …`` (and the ``HB.structure`` analogue).
_HB_DECL_RE = re.compile(
    r"^\s*HB\.(?:instance|structure)\s+Definition\s+([A-Za-z_][A-Za-z0-9_']*)"
)

#: Keywords that open an ``Inductive``/``Variant``/``CoInductive`` block
#: whose body lists constructors (``| Cn …``).  A block runs from this
#: keyword to the terminating ``.`` at end of statement.
_IND_KEYWORDS = ("Inductive", "CoInductive", "Variant")

#: Start of an inductive-family block; the family name is captured so the
#: scanner can skip it (it is already harvested as a top-level decl).
_IND_OPEN_RE = re.compile(
    r"^\s*(?:" + "|".join(_IND_KEYWORDS) + r")\s+([A-Za-z_][A-Za-z0-9_']*)"
)

#: A constructor line inside an inductive body: ``| Cn …``.  The name is
#: the bare identifier immediately following the ``|`` bar.  Constructor
#: signatures may span several lines, but the *name* always sits on the
#: bar line, so a per-line scan suffices.
_CTOR_RE = re.compile(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)")

#: Inline constructor(s) on the opener line *after* ``:=``, for the compact
#: ``Inductive T := A | B.`` / ``:= | A | B.`` form.  Applied to the text
#: following ``:=``: the first identifier (leading ``|`` optional) and each
#: ``| Cn`` thereafter.
_INLINE_CTOR_RE = re.compile(r"(?:^\s*\|?|\|)\s*([A-Za-z_][A-Za-z0-9_']*)")

#: Keywords that open a record-like block whose body lists fields (the
#: projection functions).  ``HB.mixin Record`` is matched by the same
#: opener via its ``Record`` token.
_RECORD_KEYWORDS = ("Record", "Structure", "Class")

#: Start of a record-like block.  We do not capture the structure name
#: here (it is harvested as a top-level decl by :data:`_DECL_RE`); we only
#: need to know a ``{ … }`` field list has begun.  Matches both the bare
#: forms and the ``HB.mixin Record`` form.
_RECORD_OPEN_RE = re.compile(
    r"^\s*(?:HB\.mixin\s+)?(?:" + "|".join(_RECORD_KEYWORDS) + r")\b"
)

#: A field declaration inside a record body: ``field_name : …``.  A field
#: opens either at the start of a (possibly indented) line — the common
#: multi-line layout ``{\n  f1 : ty;\n  f2 : ty;\n}`` — or right after a
#: ``{`` / ``;`` separator on the same line — the compact single-line
#: layout ``Record R := Mk { f1 : ty; f2 : ty }``.  A trailing ``:`` that
#: is *not* ``:=`` confirms a field rather than a ``:=`` body or a
#: type-ascription continuation.
_FIELD_RE = re.compile(
    r"(?:^\s*|[{;]\s*)([A-Za-z_][A-Za-z0-9_']*)\s*:(?!=)"
)


# -- maps -------------------------------------------------------------------


def _iter_entries(doc: Document):
    """Yield every Entry of ``doc`` across sections, chapters and beyond.

    The beyond compat shim aliases Section/Entry objects, so callers that
    need object-level dedup must do it themselves; for map building the
    revisits are harmless (idempotent inserts).
    """
    for section in doc.sections:
        yield from section.entries
    for chapter in doc.chapters:
        for section in chapter.sections:
            yield from section.entries
    for contrib in doc.beyond:
        yield from contrib.entries


def build_ident_map(doc: Document) -> dict[str, str]:
    """Collect ``{ident: entry_id}`` over every entry of ``doc``.

    Walks the paper-section tree, the PPL/Examples chapter tree and the
    (possibly shimmed) beyond list; the shim shares Entry objects so
    revisiting them is harmless.  Filtering and dedup rules are
    documented in the module docstring.
    """
    # Lazy import to avoid a cycle (parser imports this module).
    from .parser import slugify_label

    mapping: dict[str, str] = {}

    def consider(entry: Entry) -> None:
        for ident in entry.rocq_idents:
            if len(ident) < MIN_IDENT_LEN:
                continue
            if not _IDENT_RE.fullmatch(ident):
                continue  # qualified / operator / notation-like cells
            prev = mapping.get(ident)
            if prev is None:
                mapping[ident] = entry.id
            elif prev != entry.id and entry.id == slugify_label(ident):
                # The ident's "own" page trumps an earlier claimant.
                mapping[ident] = entry.id

    for entry in _iter_entries(doc):
        consider(entry)
    return mapping


def build_global_entry_map(three: ThreeTabDocument) -> dict[str, tuple[str, str]]:
    """Collect ``{ident: (tab, entry_id)}`` across all three tabs.

    Tabs are visited in the deterministic order :data:`ALL_TABS`
    (paper, ppl, examples).  Within and across tabs the dedup rule is
    the same as :func:`build_ident_map`: an ident's *own* page — where
    ``entry.id == slugify_label(ident)`` — always wins; otherwise the
    first claimant in tab/document order keeps the slot.
    """
    from .parser import slugify_label

    mapping: dict[str, tuple[str, str]] = {}

    def consider(tab: str, entry: Entry) -> None:
        for ident in entry.rocq_idents:
            if len(ident) < MIN_IDENT_LEN:
                continue
            if not _IDENT_RE.fullmatch(ident):
                continue
            prev = mapping.get(ident)
            if prev is None:
                mapping[ident] = (tab, entry.id)
            elif prev != (tab, entry.id) and entry.id == slugify_label(ident):
                mapping[ident] = (tab, entry.id)

    for tab in ALL_TABS:
        doc = three.tab(tab)
        for entry in _iter_entries(doc):
            consider(tab, entry)
    return mapping


def canonical_section_ids(doc: Document) -> set[str]:
    """Section ids whose lone synthetic entry has ``id == section.id``.

    A PPL/Examples H3 with no overview table becomes a Section wrapping ONE
    Entry whose id equals the section id (see
    :func:`tools.auditor.parser`).  For such sections the standalone
    ``entries/<id>.html`` page is suppressed — the section page is
    canonical and inlines the entry — so cross-references targeting that
    entry must route to ``sections/<id>.html`` instead.  This returns the
    set of those section ids for one tab document.
    """
    ids: set[str] = set()
    for chapter in doc.chapters:
        for section in chapter.sections:
            entries = section.entries
            if len(entries) == 1 and entries[0].id == section.id:
                ids.add(section.id)
    return ids


def page_suffix(entry_id: str, canonical: set[str]) -> str:
    """Route suffix for an entry link: section page if canonical else entry.

    ``canonical`` is a set of section ids (see :func:`canonical_section_ids`)
    whose entry page was suppressed; a target in that set routes to
    ``sections/<id>.html``, everything else to ``entries/<id>.html``.
    """
    if entry_id in canonical:
        return f"sections/{entry_id}.html"
    return f"entries/{entry_id}.html"


def _scan_vfile(lines: list[str]) -> "Iterator[tuple[str, int, int]]":
    """Yield ``(name, lineno, priority)`` for every indexable ident.

    ``priority`` is 0 for a top-level declaration and 1 for a
    constructor/field, so a same-file clash resolves in favour of the
    top-level decl (constructors and projections rank *below* decls within
    one file).  Three forms are recognised, each anchored at the start of a
    (possibly indented) line:

    * **Top-level declarations** (:data:`_DECL_RE`, plus named
      ``HB.instance``/``HB.structure``) — priority 0.
    * **Inductive/Variant/CoInductive constructors** — every ``| Cn …``
      line *inside* an ``Inductive``-family block, priority 1.  The block
      runs from its opening keyword to the statement-terminating ``.`` at
      end of line; constructor signatures spanning several lines are
      handled because the constructor name always sits on the bar line.
    * **Record / Structure / Class / HB.mixin Record fields** (the
      projection functions) — every ``field : ty`` entry inside a
      record body, priority 1.  The body runs from the opening keyword to
      its terminating ``.``.

    The function is line-oriented and brace/keyword driven rather than a
    full parser; it deliberately over-accepts inside a block (a stray
    ``ident : ty`` is taken as a field) but the caller's ambiguity
    exclusion and the ``code-xref`` priority ladder keep wrong links out.
    """

    def stmt_ends(text: str) -> bool:
        # A Rocq statement terminates at a ``.`` followed by whitespace or
        # end-of-line (``..``/``...`` ellipses and ``.(`` projections are
        # not statement ends, but inside these declaration bodies a bare
        # trailing ``.`` reliably closes the block).
        stripped = text.rstrip()
        return stripped.endswith(".") and not stripped.endswith("..")

    in_inductive = False
    in_record = False
    for lineno, text in enumerate(lines, start=1):
        if in_inductive:
            m = _CTOR_RE.match(text)
            if m:
                yield (m.group(1), lineno, 1)
            if stmt_ends(text):
                in_inductive = False
            continue
        if in_record:
            for fm in _FIELD_RE.finditer(text):
                yield (fm.group(1), lineno, 1)
            if stmt_ends(text):
                in_record = False
            continue

        # Not inside a block: try the openers first so the family/record
        # name is harvested as a top-level decl and the body is scanned.
        m_ind = _IND_OPEN_RE.match(text)
        if m_ind:
            yield (m_ind.group(1), lineno, 0)
            # Inline constructors after ``:=`` on the opener line — the
            # compact ``Inductive T := | A | B.`` (or ``:= A | B.``) form.
            eq = text.find(":=")
            if eq != -1:
                for cm in _INLINE_CTOR_RE.finditer(text[eq + 2 :]):
                    yield (cm.group(1), lineno, 1)
            if not stmt_ends(text):
                in_inductive = True
            continue
        if _RECORD_OPEN_RE.match(text):
            # The structure name is captured by _DECL_RE for the bare forms
            # and the ``HB.mixin Record`` form alike (the ``Record`` token
            # precedes the name in both).
            md = _DECL_RE.match(text)
            if md and len(md.group(1)) >= MIN_IDENT_LEN:
                yield (md.group(1), lineno, 0)
            # The compact single-line layout ``Record R := Mk { f : ty }``
            # carries its fields on the opener line *after* the ``{``; the
            # multi-line layout opens the brace here and lists fields on
            # following lines.  Scan whatever follows the first ``{`` so the
            # single-line case is not missed (the structure/type-ascription
            # tokens before ``{`` are excluded by slicing at the brace).
            brace = text.find("{")
            if brace != -1:
                for fm in _FIELD_RE.finditer(text[brace:]):
                    yield (fm.group(1), lineno, 1)
            if not stmt_ends(text):
                in_record = True
            continue

        m = _DECL_RE.match(text) or _HB_DECL_RE.match(text)
        if m:
            yield (m.group(1), lineno, 0)


def _build_decl_index(
    files: list[tuple[str, list[str]]],
) -> dict[str, tuple[str, int]]:
    """Build ``{ident: (key, line)}`` from pre-read ``(key, lines)`` files.

    ``key`` is whatever the caller wants to associate with a file (a
    repo-relative ``.v`` path for the local index, a dotted module name
    for the mathcomp index).  Within a single file the lower ``priority``
    wins (top-level decl beats a constructor/field of the same name);
    across *different* files any clash marks the ident ambiguous and it is
    dropped.  Idents shorter than :data:`MIN_IDENT_LEN` are excluded.
    """
    # Per-ident: the winning (key, line, priority) so far.
    first: dict[str, tuple[str, int, int]] = {}
    ambiguous: set[str] = set()

    for key, lines in files:
        for name, lineno, priority in _scan_vfile(lines):
            if len(name) < MIN_IDENT_LEN:
                continue
            existing = first.get(name)
            if existing is None:
                first[name] = (key, lineno, priority)
            elif existing[0] != key:
                ambiguous.add(name)
            elif priority < existing[2]:
                # Same file, higher-priority (top-level) sighting wins.
                first[name] = (key, lineno, priority)

    for name in ambiguous:
        first.pop(name, None)
    return {name: (key, line) for name, (key, line, _prio) in first.items()}


def build_source_index(
    theories_root: str | Path,
    *,
    repo_root: str | Path | None = None,
) -> dict[str, tuple[str, int]]:
    """Scrape ``{ident: (vfile, line)}`` from ``theories/**/*.v``.

    ``vfile`` is repository-relative (e.g. ``theories/exp/coalgebra.v``),
    suitable for :meth:`CoqdocResolver.github_url`.  Paths are made
    relative to ``repo_root`` (the directory holding ``theories/``);
    when omitted it defaults to ``theories_root``'s parent.

    Three declaration forms are indexed (see :func:`_scan_vfile`):
    top-level declarations (:data:`_DECL_KEYWORDS`, plus named
    ``HB.instance``/``HB.structure``), inductive/variant constructors, and
    record/structure/class/``HB.mixin Record`` fields (projection
    functions).  Local binders and ``Notation "…"`` string forms are not.

    Ambiguity is resolved by *exclusion*: an ident declared in more than
    one file — whether as a decl, a constructor or a field — is dropped,
    so the index never yields a wrong target.  Within one file a top-level
    decl outranks a constructor/field of the same name.  Idents shorter
    than :data:`MIN_IDENT_LEN` are excluded.
    """
    root = Path(theories_root)
    if not root.is_dir():
        return {}
    base = Path(repo_root) if repo_root is not None else root.parent

    files: list[tuple[str, list[str]]] = []
    for vfile in sorted(root.rglob("*.v")):
        try:
            rel = vfile.relative_to(base).as_posix()
        except ValueError:
            rel = vfile.as_posix()
        try:
            lines = vfile.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        files.append((rel, lines))

    return _build_decl_index(files)


# -- mathcomp external index ------------------------------------------------

#: Pinned source tags matching the *installed* mathcomp packages — see the
#: project memory (``rocq-mathcomp-ssreflect 2.5.0`` ⇒ tag
#: ``mathcomp-2.5.0`` in ``math-comp/math-comp``; ``rocq-mathcomp-analysis
#: 1.16.0`` ⇒ tag ``1.16.0`` in ``math-comp/analysis``).  Pinning to the
#: installed version avoids path/version skew (the repo layout is
#: reorganised across releases); the URLs below were verified to resolve
#: against these exact tags.
_MATHCOMP_CORE_REPO = "math-comp/math-comp"
_MATHCOMP_CORE_TAG = "mathcomp-2.5.0"
_MATHCOMP_ANALYSIS_REPO = "math-comp/analysis"
_MATHCOMP_ANALYSIS_TAG = "1.16.0"

#: Installed top-level mathcomp directories that ship in the *core*
#: ``math-comp`` repo (path inside the repo == the directory name).
_MATHCOMP_CORE_DIRS = frozenset(
    {
        "algebra",
        "boot",
        "field",
        "fingroup",
        "order",
        "solvable",
        "ssreflect",
        "character",
    }
)

#: Installed top-level dirs shipped by the ``analysis`` repo whose repo
#: path equals the directory name (``classical/…``, ``reals/…``).  The
#: ``analysis`` dir itself maps to ``theories/`` and is handled below.
_MATHCOMP_ANALYSIS_FLAT_DIRS = frozenset({"classical", "reals"})


def _mathcomp_source_url(module: str) -> str | None:
    """Map a dotted ``mathcomp.<dir>.<…>.<file>`` module to a GitHub blob.

    Returns a versioned source-file URL (no ``#L`` line, to avoid line
    skew) in the repo that actually ships that directory, or ``None`` if
    the module's top directory is not one we recognise.  The mapping was
    verified file-by-file against the pinned tags:

    * ``mathcomp.<core>.<rest>``     → ``math-comp/<core>/<rest>.v``
    * ``mathcomp.classical.<rest>``  → ``analysis/classical/<rest>.v``
    * ``mathcomp.reals.<rest>``      → ``analysis/reals/<rest>.v``
    * ``mathcomp.analysis.<rest>``   → ``analysis/theories/<rest>.v``
    """
    parts = module.split(".")
    if len(parts) < 3 or parts[0] != "mathcomp":
        return None
    top = parts[1]
    rest = "/".join(parts[2:])
    if top in _MATHCOMP_CORE_DIRS:
        repo, tag, path = _MATHCOMP_CORE_REPO, _MATHCOMP_CORE_TAG, f"{top}/{rest}.v"
    elif top in _MATHCOMP_ANALYSIS_FLAT_DIRS:
        repo, tag = _MATHCOMP_ANALYSIS_REPO, _MATHCOMP_ANALYSIS_TAG
        path = f"{top}/{rest}.v"
    elif top == "analysis":
        repo, tag = _MATHCOMP_ANALYSIS_REPO, _MATHCOMP_ANALYSIS_TAG
        path = f"theories/{rest}.v"
    else:
        return None
    return f"https://github.com/{repo}/blob/{tag}/{path}"


def _mathcomp_module_name(vfile: Path) -> str | None:
    """Read the dotted logical module name from a ``.v`` file's ``.glob``.

    coqdoc/``.glob`` files begin with an ``F<module>`` directive carrying
    the full logical path (e.g. ``Fmathcomp.analysis.measure_theory.
    dirac_measure``).  This is the authoritative module name — robust to
    the on-disk subdirectory reshuffles across releases — so we prefer it
    over reconstructing from the path.  Returns ``None`` when no sibling
    ``.glob`` exists or it lacks the directive.
    """
    glob = vfile.with_suffix(".glob")
    try:
        head = glob.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return None
    for line in head:
        if line.startswith("F"):
            return line[1:].strip()
        if not line.startswith("DIGEST"):
            break
    return None


def build_mathcomp_index(
    mathcomp_root: str | Path,
) -> dict[str, str]:
    """Scrape ``{ident: source_url}`` from the installed mathcomp sources.

    ``mathcomp_root`` is the ``…/user-contrib/mathcomp`` directory.  Each
    ``.v`` file is scanned with the same :func:`_scan_vfile` machinery as
    the local index (top-level decls + constructors + record fields), its
    logical module is read from the sibling ``.glob`` (falling back to the
    relative path), and a verified GitHub source URL is built per
    :func:`_mathcomp_source_url`.  Modules whose top directory is not
    recognised (or files lacking a resolvable URL) are skipped.

    Ambiguity exclusion and :data:`MIN_IDENT_LEN` match the local index:
    an ident appearing in more than one mathcomp module is dropped.  The
    returned map is the lowest-priority (external) tier of the resolution
    ladder, consulted only after the local source index misses.
    """
    root = Path(mathcomp_root)
    if not root.is_dir():
        return {}

    files: list[tuple[str, list[str]]] = []
    module_url: dict[str, str] = {}
    for vfile in sorted(root.rglob("*.v")):
        module = _mathcomp_module_name(vfile)
        if module is None:
            # Fall back to reconstructing ``mathcomp.<rel-with-dots>``.
            try:
                rel = vfile.relative_to(root.parent).with_suffix("")
            except ValueError:
                continue
            module = ".".join(rel.parts)
        url = _mathcomp_source_url(module)
        if url is None:
            continue
        try:
            lines = vfile.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        files.append((module, lines))
        module_url[module] = url

    decl_index = _build_decl_index(files)
    return {
        ident: module_url[module] for ident, (module, _line) in decl_index.items()
    }


def find_mathcomp_root() -> Path | None:
    """Locate the installed ``…/user-contrib/mathcomp`` source directory.

    Searches the active opam switch (``$OPAM_SWITCH_PREFIX``) first, then
    common ``COQLIB``/``ROCQLIB`` roots, returning the first existing
    ``mathcomp`` directory.  Returns ``None`` when none is found (e.g. the
    package is not installed), in which case external linking is skipped.
    """
    import os

    candidates: list[Path] = []
    for var in ("OPAM_SWITCH_PREFIX", "COQLIB", "ROCQLIB"):
        prefix = os.environ.get(var)
        if not prefix:
            continue
        p = Path(prefix)
        candidates.append(p / "lib" / "coq" / "user-contrib" / "mathcomp")
        candidates.append(p / "lib" / "rocq" / "user-contrib" / "mathcomp")
        candidates.append(p / "user-contrib" / "mathcomp")
        candidates.append(p / "coq" / "user-contrib" / "mathcomp")
    for cand in candidates:
        if cand.is_dir():
            return cand
    return None


# -- shared linkify core ----------------------------------------------------

#: A resolver maps an ident to a :class:`LinkTarget` or ``None``.
#: ``None`` means "leave the token plain" (unknown ident or self-link).
Resolver = Callable[[str], "LinkTarget | None"]


class LinkTarget:
    """One resolved anchor: ``href``, a ``code-xref`` class suffix and
    optional extra tag attributes.

    * ``class_suffix`` is appended *inside* the ``class="code-xref…"``
      attribute — ``""`` for entry links, ``" code-xref-src"`` for local
      source links, ``" code-xref-ext"`` for mathcomp-external links.
    * ``attrs`` is verbatim markup placed after the ``href`` attribute —
      empty for internal links, ``' target="_blank" rel="noopener"'`` for
      external links so they open in a new tab.
    """

    __slots__ = ("href", "class_suffix", "attrs")

    def __init__(self, href: str, class_suffix: str = "", attrs: str = "") -> None:
        self.href = href
        self.class_suffix = class_suffix
        self.attrs = attrs


def _anchor(escaped_tok: str, target: "LinkTarget") -> str:
    """Render the ``<a …>escaped_tok</a>`` for a resolved link target."""
    return (
        f'<a class="code-xref{target.class_suffix}" '
        f'href="{target.href}"{target.attrs}>'
        f"{escaped_tok}</a>"
    )


def _already_linked(html: str) -> set[str]:
    """Idents already wrapped in a ``code-xref`` anchor within ``html``.

    Pre-seeds the first-occurrence-only set so a token linked by an earlier
    pass is not re-linked (at a *later* occurrence) by a subsequent one,
    keeping the composed passes idempotent.
    """
    return {
        html_mod.unescape(m.group(1)) for m in _LINKED_XREF_RE.finditer(html)
    }


def _linkify_html(highlighted_html: str, resolve: Resolver) -> str:
    """Wrap the FIRST resolvable occurrence of each name token in an anchor.

    Only the first occurrence of a given identifier within this one snippet
    is linked; later occurrences of the same ident are left as plain name
    tokens so a snippet mentioning ``foo`` a dozen times yields a single
    ``code-xref`` rather than a wall of links.  Idents already wrapped by a
    previous pass are pre-seeded so the policy is stable across the per-tab
    and global passes.
    """
    linked: set[str] = _already_linked(highlighted_html)

    def repl(m: re.Match[str]) -> str:
        cls, escaped_tok = m.group(1), m.group(2)
        ident = html_mod.unescape(escaped_tok)
        if ident in linked:
            return m.group(0)
        target = resolve(ident)
        if target is None:
            return m.group(0)
        linked.add(ident)
        return f'<span class="{cls}">{_anchor(escaped_tok, target)}</span>'

    return _NAME_SPAN_RE.sub(repl, highlighted_html)


def _linkify_prose(prose_html: str, resolve: Resolver) -> str:
    """Wrap resolvable ``<code>`` prose spans in ``code-xref`` anchors.

    Only ``<code>`` bodies that, after HTML-unescape, are a single
    identifier (``_IDENT_RE.fullmatch``), at least :data:`MIN_IDENT_LEN`
    long and resolve to a target are wrapped.  Math / notation spans
    never match the regex and are returned verbatim, as are self-links
    and unknown idents.
    """
    if not prose_html or "<code>" not in prose_html:
        return prose_html

    linked: set[str] = _already_linked(prose_html)

    def repl(m: re.Match[str]) -> str:
        escaped_tok = m.group(1)
        ident = html_mod.unescape(escaped_tok)
        if len(ident) < MIN_IDENT_LEN or not _IDENT_RE.fullmatch(ident):
            return m.group(0)
        if ident in linked:
            return m.group(0)
        target = resolve(ident)
        if target is None:
            return m.group(0)
        linked.add(ident)
        return f"<code>{_anchor(escaped_tok, target)}</code>"

    return _CODE_SPAN_RE.sub(repl, prose_html)


def _walk_document(
    doc: Document,
    resolve_for: Callable[[str | None], Resolver],
) -> None:
    """Apply ``resolve_for(owner_id)`` to every snippet/prose of ``doc``.

    ``resolve_for`` is given the owning entry id (or ``None`` for
    section-/chapter-level prose and snippets) and returns the
    :data:`Resolver` to use for that owner.  Snippets are deduplicated by
    object identity so the beyond compat shim (which aliases Section /
    Entry objects) processes each exactly once; the prose passes are
    idempotent so re-touching aliased prose is harmless.
    """
    seen: set[int] = set()

    def do_snippets(snips: list[CoqSnippet], owner: str | None) -> None:
        resolve = resolve_for(owner)
        for s in snips:
            if id(s) in seen:
                continue
            seen.add(id(s))
            s.highlighted_html = _linkify_html(s.highlighted_html, resolve)

    def do_entry(entry: Entry) -> None:
        resolve = resolve_for(entry.id)
        entry.statement_html = _linkify_prose(entry.statement_html, resolve)
        if entry.detail is not None:
            do_snippets(entry.detail.snippets, entry.id)
            entry.detail.prose_html = _linkify_prose(entry.detail.prose_html, resolve)

    def do_section(section) -> None:
        none_resolve = resolve_for(None)
        section.intro_html = _linkify_prose(section.intro_html, none_resolve)
        section.notes_html = _linkify_prose(section.notes_html, none_resolve)
        do_snippets(section.snippets, None)
        for entry in section.entries:
            do_entry(entry)

    for section in doc.sections:
        do_section(section)
    for chapter in doc.chapters:
        none_resolve = resolve_for(None)
        chapter.intro_html = _linkify_prose(chapter.intro_html, none_resolve)
        chapter.notes_html = _linkify_prose(chapter.notes_html, none_resolve)
        for section in chapter.sections:
            do_section(section)
    for contrib in doc.beyond:
        none_resolve = resolve_for(None)
        contrib.intro_html = _linkify_prose(contrib.intro_html, none_resolve)
        contrib.notes_html = _linkify_prose(contrib.notes_html, none_resolve)
        do_snippets(contrib.snippets, None)
        for entry in contrib.entries:
            do_entry(entry)
    # ``preamble_html`` is rendered ONLY on the depth-1 ``index.html``
    # landing (every other field embeds in depth-2 pages); its hrefs need
    # a different relative prefix and are handled by the global pass'
    # :func:`_linkify_preamble`, so it is deliberately skipped here.


# -- dependency edges (graph) -----------------------------------------------

#: Strips every HTML tag, leaving the text payload.  Used to recover the
#: plain identifier stream from a snippet's Pygments HTML or a prose
#: ``<code>`` block regardless of whether the linkify pass has already
#: wrapped some tokens in ``<a>`` anchors (so edge extraction is order
#: independent w.r.t. :func:`linkify_all`).
_TAG_RE = re.compile(r"<[^>]+>")


def _entry_text_idents(entry: Entry) -> set[str]:
    """Collect the identifier tokens an entry's code/prose mentions.

    Recovers a plain-text stream from the entry's statement, detail prose
    and every detail snippet (HTML tags stripped, entities unescaped),
    tokenises it with :data:`_IDENT_RE` and returns the distinct tokens at
    least :data:`MIN_IDENT_LEN` long.  This is the raw mention set; the
    caller maps it through the global entry map to obtain dependency
    targets.  It is robust to the linkify pass having already wrapped some
    tokens in anchors (the tags are stripped either way).
    """
    chunks: list[str] = []
    if entry.statement_html:
        chunks.append(entry.statement_html)
    if entry.detail is not None:
        if entry.detail.prose_html:
            chunks.append(entry.detail.prose_html)
        for snip in entry.detail.snippets:
            chunks.append(snip.highlighted_html)
    idents: set[str] = set()
    for chunk in chunks:
        text = html_mod.unescape(_TAG_RE.sub(" ", chunk))
        for m in _IDENT_RE.finditer(text):
            tok = m.group(0)
            if len(tok) >= MIN_IDENT_LEN:
                idents.add(tok)
    return idents


def build_entry_edges(
    three: ThreeTabDocument,
) -> list[tuple[tuple[str, str], tuple[str, str]]]:
    """Derive directed dependency edges between entries across all tabs.

    An edge ``A -> B`` is emitted when entry ``A``'s code/prose mentions an
    identifier *owned* by a different entry ``B`` (per the cross-tab
    :func:`build_global_entry_map`).  This is exactly the relation the
    snippet/prose linkifier uses to turn an ident token into a link to its
    defining entry, surfaced here as graph data.

    Each endpoint is a ``(tab, entry_id)`` pair.  Self-edges (``A`` to
    itself) are dropped and duplicates are removed; the returned list is
    sorted for determinism.
    """
    entry_map = build_global_entry_map(three)
    # Index every entry by (tab, id) so we only emit edges between known
    # nodes (mirrors the node set the renderer builds).
    known: set[tuple[str, str]] = set()
    owners: list[tuple[str, str, Entry]] = []
    for tab in ALL_TABS:
        doc = three.tab(tab)
        seen: set[int] = set()
        for entry in _iter_entries(doc):
            if id(entry) in seen:
                continue
            seen.add(id(entry))
            known.add((tab, entry.id))
            owners.append((tab, entry.id, entry))

    edges: set[tuple[tuple[str, str], tuple[str, str]]] = set()
    for tab, eid, entry in owners:
        src = (tab, eid)
        for ident in _entry_text_idents(entry):
            tgt = entry_map.get(ident)
            if tgt is None or tgt == src or tgt not in known:
                continue
            edges.add((src, tgt))
    return sorted(edges)


def attach_entry_relations(three: ThreeTabDocument) -> ThreeTabDocument:
    """Populate each entry's ``mentions`` cross-refs; returns ``three``.

    Reuses :func:`build_entry_edges` — the same Rocq-identifier overlap the
    linkifier turns into inline links.  That relation is a **co-occurrence**,
    not a dependency: ``A -> B`` merely records that *some token* in ``A``'s
    statement / prose / snippet text is an identifier ``B`` documents.  A
    prose mention carries no direction (Thm 4.18's text pointing the reader
    *forward* to Thm 4.19 produced, verbatim, a "Thm 4.19 is used by Thm
    4.18" claim), and the relation is demonstrably symmetric in the data:
    dozens of pairs mention each other.

    So the pair is filed **undirected**, as ``kind='mentions'`` with
    ``via='doc'``, on *both* endpoints — never as ``uses`` / ``used-by``,
    which are reserved for the proof-level ``.glob`` relation attached by
    :func:`attach_glob_relations`.  ``target``/``tab``/``label`` describe
    the partner entry, so the renderer can still build a cross-tab href.

    Refs are appended to the entry's existing ``cross_refs`` (the synthetic
    ``beyond`` ref is preserved) and deduplicated by
    ``(kind, target, tab)``.  Entry objects shared across the beyond compat
    shim are updated exactly once (dedup by object id).
    """
    edges = build_entry_edges(three)

    # (tab, id) -> the owning Entry object (first sighting wins; aliased
    # shim objects share the same key so this is a genuine 1:1).
    entry_by_key: dict[tuple[str, str], Entry] = {}
    for tab in ALL_TABS:
        doc = three.tab(tab)
        for entry in _iter_entries(doc):
            entry_by_key.setdefault((tab, entry.id), entry)

    # Symmetrise: an edge in either direction makes the two entries
    # partners in exactly one undirected co-reference.
    partners: dict[tuple[str, str], set[tuple[str, str]]] = {}
    for src, tgt in edges:
        partners.setdefault(src, set()).add(tgt)
        partners.setdefault(tgt, set()).add(src)

    def label_for(key: tuple[str, str]) -> str:
        target = entry_by_key.get(key)
        return target.paper_label if target is not None else key[1]

    def append_refs(
        entry: Entry, kind: str, targets: set[tuple[str, str]]
    ) -> None:
        existing = {(x.kind, x.target, x.tab) for x in entry.cross_refs}
        for t_tab, t_id in sorted(targets):
            triple = (kind, t_id, t_tab)
            if triple in existing:
                continue
            existing.add(triple)
            entry.cross_refs.append(
                CrossRef(
                    kind=kind,
                    target=t_id,
                    label=label_for((t_tab, t_id)),
                    tab=t_tab,
                    via="doc",
                )
            )

    seen: set[int] = set()
    for key, entry in entry_by_key.items():
        if id(entry) in seen:
            continue
        seen.add(id(entry))
        append_refs(entry, MENTION_KIND, partners.get(key, set()))
    return three



def attach_glob_relations(
    three: ThreeTabDocument,
    edges: Iterable[tuple[tuple[str, str], tuple[str, str]]],
) -> ThreeTabDocument:
    """Upgrade each entry's Uses / Used-by panel with REAL ``.glob`` deps.

    ``edges`` is the proof-level dependency relation
    (:func:`tools.auditor.glob_deps.build_glob_relation`): ``A -> B`` when a
    Coq object entry ``A`` documents *uses* an object entry ``B`` documents,
    as recorded in the ``.glob`` files.  This is the same edge set the
    dependency graph draws solid — surfaced here as per-card navigation, so
    an entry page links to exactly what its proof rests on and to what rests
    on it, without the reader having to open the graph.

    For every entry it:

    * marks an existing ``uses`` / ``used-by`` ref that the ``.glob`` data
      confirms with ``via='glob'``;
    * **demotes** any ``uses`` / ``used-by`` ref the ``.glob`` data does
      *not* confirm to an undirected :data:`MENTION_KIND` co-reference.
      A directional dependency claim the proofs do not back is exactly the
      class of falsehood this panel used to publish ("Thm 4.19 · Used by ·
      Thm 4.18", minted by a forward-pointing sentence in Thm 4.18's
      prose), so the invariant is enforced here rather than trusted:
      **after this pass every ``uses`` / ``used-by`` ref carries
      ``via='glob'``**;
    * appends a ``via='glob'`` ref for a real dependency the prose never
      named — the case that motivates parsing ``.glob`` at all;
    * drops a ``mentions`` ref for a partner this entry already has a
      proof-level relation with (the strong relation subsumes the weak
      one, in either direction); and
    * re-orders the refs: proof-backed ``uses`` then ``used-by``, then the
      doc co-references, each alphabetically by label.

    Idempotent (dedup by ``(kind, target, tab)``).  On an empty ``edges``
    the demotion still runs: a build without ``.glob`` data then shows an
    honest co-reference-only panel instead of unbacked dependency claims.
    """
    entry_by_key: dict[tuple[str, str], Entry] = {}
    for tab in ALL_TABS:
        doc = three.tab(tab)
        for entry in _iter_entries(doc):
            entry_by_key.setdefault((tab, entry.id), entry)

    uses: dict[tuple[str, str], set[tuple[str, str]]] = {}
    used_by: dict[tuple[str, str], set[tuple[str, str]]] = {}
    for src, tgt in edges:
        uses.setdefault(src, set()).add(tgt)
        used_by.setdefault(tgt, set()).add(src)

    def label_for(key: tuple[str, str]) -> str:
        target = entry_by_key.get(key)
        return target.paper_label if target is not None else key[1]

    seen: set[int] = set()
    for key, entry in entry_by_key.items():
        if id(entry) in seen:
            continue
        seen.add(id(entry))
        real = {"uses": uses.get(key, set()), "used-by": used_by.get(key, set())}
        if not (real["uses"] or real["used-by"] or entry.cross_refs):
            continue
        # 1. Confirm the refs the .glob data backs; DEMOTE the rest to an
        #    undirected co-reference (a dependency claim the proofs do not
        #    back must never render in a Uses / Used-by slot).
        present: dict[str, set[tuple[str, str]]] = {k: set() for k in _RELATION_KINDS}
        for ref in entry.cross_refs:
            if ref.kind not in _RELATION_KINDS:
                continue
            pair = (ref.tab, ref.target)
            if pair in real[ref.kind]:
                present[ref.kind].add(pair)
                ref.via = "glob"
            else:
                ref.kind = MENTION_KIND
                ref.via = "doc"
        # 2. Append the real dependencies no prose mentioned.
        for kind in _RELATION_KINDS:
            for t_tab, t_id in sorted(real[kind] - present[kind]):
                entry.cross_refs.append(
                    CrossRef(
                        kind=kind,
                        target=t_id,
                        label=label_for((t_tab, t_id)),
                        tab=t_tab,
                        via="glob",
                    )
                )
        # 3. A partner this entry really depends on (either direction) is
        #    already stated the strong way; the weak co-reference to the
        #    same entry is then pure duplication.  Drop it, and collapse
        #    the duplicates the demotion in (1) may have created.
        proof_partners = real["uses"] | real["used-by"]
        kept: list[CrossRef] = []
        seen_triples: set[tuple[str, str, str]] = set()
        for ref in entry.cross_refs:
            if ref.kind == MENTION_KIND and (ref.tab, ref.target) in proof_partners:
                continue
            triple = (ref.kind, ref.target, ref.tab)
            if triple in seen_triples:
                continue
            seen_triples.add(triple)
            kept.append(ref)
        entry.cross_refs = kept
        # 4. Proof-backed links first, then the doc co-references.
        ordered = [
            x
            for x in entry.cross_refs
            if x.kind not in _RELATION_KINDS and x.kind != MENTION_KIND
        ]
        for kind in (*_RELATION_KINDS, MENTION_KIND):
            ordered = ordered + sorted(
                (x for x in entry.cross_refs if x.kind == kind),
                key=lambda x: (x.via != "glob", x.label.lower(), x.tab),
            )
        entry.cross_refs = ordered
    return three


# -- per-tab pass (legacy / single-tab) -------------------------------------


def linkify_document(doc: Document) -> Document:
    """Linkify every snippet/prose of ``doc`` in place; returns ``doc``.

    Same-tab pass: links an ident to another entry of *this* document
    with a uniform ``../entries/<id>.html`` href, suppressing self-links.
    Run by the single-tab :func:`~tools.auditor.parser.parse` path and
    relied on by the goldens.  The global :func:`linkify_all` pass later
    mops up whatever this pass leaves plain.
    """
    mapping = build_ident_map(doc)
    if not mapping:
        return doc
    canonical = canonical_section_ids(doc)

    def resolve_for(owner: str | None) -> Resolver:
        def resolve(ident: str) -> LinkTarget | None:
            target = mapping.get(ident)
            if target is None or target == owner:
                return None
            return LinkTarget(f"{_HREF_PREFIX}{page_suffix(target, canonical)}")

        return resolve

    _walk_document(doc, resolve_for)
    return doc


# -- global pass (cross-tab + source fallback) ------------------------------


def linkify_all(
    three: ThreeTabDocument,
    *,
    resolver: CoqdocResolver,
    theories_root: str | Path,
    repo_root: str | Path | None = None,
    mathcomp_root: str | Path | None = None,
) -> ThreeTabDocument:
    """Global linkify pass across all three tabs; returns ``three``.

    For each name token / prose ``<code>`` ident in a snippet owned by
    ``(tab, owner_entry)`` the resolution order is:

    1. self-link (ident maps to ``owner_entry`` in this tab) → leave plain;
    2. global entry map → link to that entry page with a tab-aware href
       (same tab ``../entries/X.html``; cross tab
       ``../../<tab>/entries/X.html``);
    3. local source index → absolute GitHub blob ``#L`` line, class
       ``code-xref code-xref-src``;
    4. mathcomp external index → versioned mathcomp source-file URL opened
       in a new tab, class ``code-xref code-xref-ext``;
    5. otherwise leave plain.

    A project-local definition therefore always wins over a mathcomp one
    of the same name (step 3 before step 4).  ``mathcomp_root`` points at
    the installed ``…/user-contrib/mathcomp`` directory; when omitted it
    is auto-located via :func:`find_mathcomp_root`, and if still not found
    (package absent) mathcomp idents simply stay plain.

    Composes with :func:`linkify_document`: the per-tab pass has already
    wrapped same-tab entry idents, so step 2's same-tab branch only ever
    fires on tokens the per-tab pass skipped (and re-linking is a no-op
    by idempotency anyway).
    """
    entry_map = build_global_entry_map(three)
    source_index = build_source_index(theories_root, repo_root=repo_root)
    mc_root = mathcomp_root if mathcomp_root is not None else find_mathcomp_root()
    mathcomp_index = build_mathcomp_index(mc_root) if mc_root is not None else {}
    # Per-tab set of collapsed section ids (single synthetic entry with
    # id == section.id): those entry pages are suppressed, so a link to
    # them must route to sections/<id>.html — see :func:`page_suffix`.
    canonical_by_tab = {t: canonical_section_ids(three.tab(t)) for t in ALL_TABS}

    def fallback_target(ident: str) -> LinkTarget | None:
        """Local source link (preferred) else mathcomp-external link."""
        src = source_index.get(ident)
        if src is not None:
            vfile, line = src
            return LinkTarget(resolver.github_url(vfile, line), " code-xref-src")
        url = mathcomp_index.get(ident)
        if url is not None:
            return LinkTarget(
                url, " code-xref-ext", ' target="_blank" rel="noopener"'
            )
        return None

    for tab in ALL_TABS:
        doc = three.tab(tab)

        def resolve_for(owner: str | None, _tab: str = tab) -> Resolver:
            # Depth-2 pages (sections/entries/beyond): own tab root is one
            # level up; another tab is two up then into ``<tab>/``.
            def resolve(ident: str) -> LinkTarget | None:
                hit = entry_map.get(ident)
                if hit is not None:
                    target_tab, target_id = hit
                    if target_tab == _tab and target_id == owner:
                        return None  # self-link on its own page
                    if target_tab == _tab:
                        href = (
                            f"{_HREF_PREFIX}"
                            f"{page_suffix(target_id, canonical_by_tab[_tab])}"
                        )
                    else:
                        href = (
                            f"../../{target_tab}/"
                            f"{page_suffix(target_id, canonical_by_tab[target_tab])}"
                        )
                    return LinkTarget(href)
                return fallback_target(ident)

            return resolve

        _walk_document(doc, resolve_for)

        # The preamble renders on the depth-1 ``<tab>/index.html`` landing,
        # so its relative hrefs drop one ``../`` level: same tab is
        # ``entries/X.html``, another tab is ``../<tab>/entries/X.html``.
        # There is no "owner entry" on the landing, so no self-links.
        def preamble_resolve(ident: str, _tab: str = tab) -> LinkTarget | None:
            hit = entry_map.get(ident)
            if hit is not None:
                target_tab, target_id = hit
                if target_tab == _tab:
                    href = page_suffix(target_id, canonical_by_tab[_tab])
                else:
                    href = (
                        f"../{target_tab}/"
                        f"{page_suffix(target_id, canonical_by_tab[target_tab])}"
                    )
                return LinkTarget(href)
            return fallback_target(ident)

        doc.preamble_html = _linkify_prose(doc.preamble_html, preamble_resolve)
    return three


__all__ = [
    "MENTION_KIND",
    "MIN_IDENT_LEN",
    "LinkTarget",
    "attach_entry_relations",
    "attach_glob_relations",
    "build_entry_edges",
    "build_global_entry_map",
    "build_ident_map",
    "build_mathcomp_index",
    "build_source_index",
    "canonical_section_ids",
    "find_mathcomp_root",
    "linkify_all",
    "linkify_document",
    "page_suffix",
]
