"""Frozen JSON schema for the auditor dashboard data model.

This module is the contract between the parser (M1/M3 — this agent) and the
templates (M2/M4 — sibling agent).  Both sides import from here, and any
deviation breaks the integration.

Output JSON: ``site/auditor/data.json``.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any


# -- atomic value types ------------------------------------------------------


@dataclass
class RocqFile:
    """A Rocq source file referenced by an entry."""

    path: str
    section: str | None
    github_url: str
    coqdoc_url: str | None
    coqdoc_anchor: str | None


@dataclass
class CrossRef:
    """A reference from one entry / section to another piece of content.

    ``tab`` names the tab that owns ``target`` (``"paper"`` | ``"ppl"`` |
    ``"examples"``).  It is empty for same-tab / tab-agnostic refs (the
    synthetic ``beyond`` ref, section refs); the ``uses`` / ``used-by``
    relation refs derived from Rocq-identifier overlap set it so the
    renderer can build a cross-tab href when it differs from the current
    tab.
    """

    kind: str  # "section" | "entry" | "beyond" | "blueprint" | "uses" | "used-by"
    target: str
    label: str
    tab: str = ""


@dataclass
class CoqSnippet:
    """A Pygments-highlighted Coq code block."""

    source_file: str
    source_section: str | None
    highlighted_html: str  # Pygments output, language=coq
    # Newline-count of the raw source the snippet was extracted from.
    # Populated by the parser at normalise time; fuels the per-chapter
    # LoC counter on the new PPL/Examples chapter cards.  Defaults to
    # 0 for legacy callers that don't set it.
    line_count: int = 0


@dataclass
class NoteBlock:
    """A blockquote / aside paragraph attached to an entry's detail."""

    kind: str  # "note" | "warning" | "info"
    html: str


@dataclass
class OverviewRow:
    """One row of a chapter/section overview table.

    ``label`` is the leftmost "Item" cell (already HTML, or a plain paper
    label); ``statement_html`` is the optional middle column (empty when
    the source table has only 2 columns); ``rocq_html`` is the trailing
    Rocq column (comma-joined ``<code>`` identifiers or a file path).
    """

    label: str
    statement_html: str = ""
    rocq_html: str = ""
    # When this row maps 1:1 to a section, its id: the overview table then
    # renders the label as a link to that section, making the table the
    # chapter's navigable index (so the redundant section-card grid is dropped).
    section_id: str = ""


@dataclass
class EntryDetail:
    """The H3-level detail block backing an entry."""

    prose_html: str
    notes: list[NoteBlock] = field(default_factory=list)
    snippets: list[CoqSnippet] = field(default_factory=list)


@dataclass
class Entry:
    """A single paper-statement -> Rocq-identifier row."""

    id: str  # "def-2-1", "thm-6-5", "lem-2-8-2-10"
    paper_label: str  # verbatim "Def 2.1"
    paper_kind: str  # "Def" | "Thm" | "Lem" | "Prop" | "Cat" | "Fubini" | "Cor" | "Other"
    paper_number: str | None  # "2.1", "6.5", null
    paper_section_id: str
    statement_html: str
    rocq_idents: list[str]
    rocq_files: list[RocqFile]
    status: list[str]  # subset of axiom-free|regression-anchor|beyond-paper|discharged-deferred|gap
    detail: EntryDetail | None
    cross_refs: list[CrossRef] = field(default_factory=list)


@dataclass
class Section:
    """A paper-§ H2 section (e.g. "§ 2 — Cones") or a PPL/Examples H3.

    Paper-tab usage leaves ``chapter_id`` and ``snippets`` at their
    defaults; PPL/Examples sections set ``chapter_id`` to the parent
    :class:`Chapter`'s id and may attach section-level ``snippets``
    (the ``coq`` blocks that belong to the whole H3, not to any single
    headline-table row).
    """

    id: str
    paper_section: str
    paper_section_number: str
    title: str
    intro_html: str
    entries: list[Entry] = field(default_factory=list)
    notes_html: str = ""
    # PPL/Examples additive: parent Chapter id; "" on Paper sections.
    chapter_id: str = ""
    # PPL/Examples additive: H3-level code blocks shown above the
    # per-entry detail.  Empty on Paper sections.
    snippets: list[CoqSnippet] = field(default_factory=list)
    # PPL/Examples additive: a compact statement<->Rocq overview table
    # rendered atop the section page (one row per entry).  Empty on
    # Paper sections.
    overview: list[OverviewRow] = field(default_factory=list)


@dataclass
class ChapterStats:
    """Pre-computed counts shown on chapter cards and chapter pages.

    Set once at parse-time by ``normalise`` so templates don't recompute
    per-render.  Used by the new PPL/Examples chapter cards and the
    stats line on the chapter landing page.
    """

    n_sections: int = 0
    n_entries: int = 0
    n_defs: int = 0          # entries with paper_kind == "Def"
    n_thms: int = 0          # paper_kind in {Thm, Lem, Prop, Cor, Cat, Fubini}
    n_snippets: int = 0      # total snippets across all sections + entries
    loc: int = 0             # sum of snippet line counts


@dataclass
class Chapter:
    """A 'Beyond the paper — <title>' H2 chapter, owning a set of Sections.

    The chapter holds high-level intro prose at H2 level; the per-section
    detail lives one level down in its :class:`Section` list (each H3
    sub-heading of PPL.md / EXAMPLES.md).  Carries the same kind of
    summary stats used by the new chapter-card progress bar.
    """

    id: str                                  # "ppl-ch-the-surface-language"
    title: str                               # H2 minus "Beyond the paper — "
    intro_html: str                          # H2-level prose
    sections: list[Section] = field(default_factory=list)
    notes_html: str = ""
    stats: ChapterStats = field(default_factory=ChapterStats)
    # A compact overview table rendered atop the chapter page: for PPL
    # chapters, the H2-level "Construction | Rocq" rows; for Examples
    # chapters (no H2 table), one synthesised row per section.
    overview: list[OverviewRow] = field(default_factory=list)


@dataclass
class BeyondContrib:
    """An H3-level contribution in the 'Beyond the paper' chapter."""

    id: str
    title: str
    intro_html: str
    entries: list[Entry] = field(default_factory=list)
    snippets: list[CoqSnippet] = field(default_factory=list)
    notes_html: str = ""
    # Parent H2 chapter heading (with the "Beyond the paper — " prefix
    # stripped).  Empty string for the synthetic chapter-overview contrib.
    # Used by the per-tab landing template to group H3 cards under their
    # parent chapter, mirroring the Paper tab's §§ → entries hierarchy.
    chapter: str = ""


@dataclass
class GapEntry:
    """A row from 'What is not formalised'."""

    id: str
    paper_label: str
    description_html: str
    reason_html: str


@dataclass
class AxiomAnchors:
    """Axiom-budget anchors highlighted on the index page."""

    regression: str
    headlines: list[str] = field(default_factory=list)


@dataclass
class BuildMeta:
    """Build provenance dumped into every page footer."""

    commit: str
    built_at: str
    auditor_lines: int


@dataclass
class Document:
    """Top-level document: the whole dashboard in one JSON blob."""

    preamble_html: str
    sections: list[Section] = field(default_factory=list)
    # PPL/Examples additive: H2 "Beyond the paper — X" chapters with
    # nested Sections (each H3) and per-entry detail.  Paper-tab parses
    # leave this empty; the Paper tab still uses ``sections`` + ``beyond``.
    # On PPL/Examples the parser also synthesises a flat ``beyond`` view
    # of ``chapters[*].sections[*]`` (compat shim) so legacy tests pass.
    chapters: list[Chapter] = field(default_factory=list)
    beyond: list[BeyondContrib] = field(default_factory=list)
    gaps: list[GapEntry] = field(default_factory=list)
    verify_instructions_html: str = ""
    axiom_anchors: AxiomAnchors = field(
        default_factory=lambda: AxiomAnchors(regression="", headlines=[])
    )
    build_meta: BuildMeta = field(
        default_factory=lambda: BuildMeta(commit="", built_at="", auditor_lines=0)
    )


# -- three-tab top level ----------------------------------------------------


# String literals used as tab identifiers (URL slug + ctx field).
TAB_PAPER = "paper"
TAB_PPL = "ppl"
TAB_EXAMPLES = "examples"
ALL_TABS = (TAB_PAPER, TAB_PPL, TAB_EXAMPLES)


@dataclass
class ThreeTabDocument:
    """Top-level dashboard document: Paper + PPL + Examples tabs.

    Each tab is an independent :class:`Document`. ``build_meta`` is shared
    (provenance is per build, not per tab) and supersedes any per-Document
    ``build_meta`` for footer rendering / data export.
    """

    paper: Document
    ppl: Document
    examples: Document
    build_meta: BuildMeta = field(
        default_factory=lambda: BuildMeta(commit="", built_at="", auditor_lines=0)
    )

    def tab(self, name: str) -> Document:
        """Return the Document for the requested tab string."""
        if name == TAB_PAPER:
            return self.paper
        if name == TAB_PPL:
            return self.ppl
        if name == TAB_EXAMPLES:
            return self.examples
        raise KeyError(f"unknown tab {name!r} (expected one of {ALL_TABS})")


# Transitional alias — keep the old name resolvable for callers that
# imported ``TwoTabDocument`` directly. New code should use
# :class:`ThreeTabDocument`.
TwoTabDocument = ThreeTabDocument


# -- serialisation ----------------------------------------------------------


def to_dict(doc: Document) -> dict[str, Any]:
    """Convert a Document to a plain JSON-serialisable dict."""
    return asdict(doc)


def three_tab_to_dict(doc: ThreeTabDocument) -> dict[str, Any]:
    """Convert a ThreeTabDocument to a plain JSON-serialisable dict.

    The combined export carries one entry per tab plus the shared build
    metadata at the top level.
    """
    return {
        "paper": asdict(doc.paper),
        "ppl": asdict(doc.ppl),
        "examples": asdict(doc.examples),
        "build_meta": asdict(doc.build_meta),
    }


# Transitional alias — see ``TwoTabDocument`` above.
two_tab_to_dict = three_tab_to_dict


def from_dict(payload: dict[str, Any]) -> Document:
    """Reverse of :func:`to_dict` — useful for tests and for the UI agent."""

    def _rocq(rf: dict[str, Any]) -> RocqFile:
        return RocqFile(**rf)

    def _xref(xr: dict[str, Any]) -> CrossRef:
        return CrossRef(
            kind=xr["kind"],
            target=xr["target"],
            label=xr["label"],
            tab=xr.get("tab", ""),
        )

    def _snip(s: dict[str, Any]) -> CoqSnippet:
        return CoqSnippet(**s)

    def _note(n: dict[str, Any]) -> NoteBlock:
        return NoteBlock(**n)

    def _orow(r: dict[str, Any]) -> OverviewRow:
        return OverviewRow(
            label=r["label"],
            statement_html=r.get("statement_html", ""),
            rocq_html=r.get("rocq_html", ""),
            section_id=r.get("section_id", ""),
        )

    def _detail(d: dict[str, Any] | None) -> EntryDetail | None:
        if d is None:
            return None
        return EntryDetail(
            prose_html=d["prose_html"],
            notes=[_note(n) for n in d.get("notes", [])],
            snippets=[_snip(s) for s in d.get("snippets", [])],
        )

    def _entry(e: dict[str, Any]) -> Entry:
        return Entry(
            id=e["id"],
            paper_label=e["paper_label"],
            paper_kind=e["paper_kind"],
            paper_number=e.get("paper_number"),
            paper_section_id=e["paper_section_id"],
            statement_html=e["statement_html"],
            rocq_idents=list(e.get("rocq_idents", [])),
            rocq_files=[_rocq(f) for f in e.get("rocq_files", [])],
            status=list(e.get("status", [])),
            detail=_detail(e.get("detail")),
            cross_refs=[_xref(x) for x in e.get("cross_refs", [])],
        )

    def _section(s: dict[str, Any]) -> Section:
        return Section(
            id=s["id"],
            paper_section=s["paper_section"],
            paper_section_number=s["paper_section_number"],
            title=s["title"],
            intro_html=s["intro_html"],
            entries=[_entry(e) for e in s.get("entries", [])],
            notes_html=s.get("notes_html", ""),
            chapter_id=s.get("chapter_id", ""),
            snippets=[_snip(sn) for sn in s.get("snippets", [])],
            overview=[_orow(r) for r in s.get("overview", [])],
        )

    sections = [_section(s) for s in payload.get("sections", [])]
    chapters = [
        Chapter(
            id=c["id"],
            title=c["title"],
            intro_html=c["intro_html"],
            sections=[_section(s) for s in c.get("sections", [])],
            notes_html=c.get("notes_html", ""),
            stats=ChapterStats(**(c.get("stats") or {})),
            overview=[_orow(r) for r in c.get("overview", [])],
        )
        for c in payload.get("chapters", [])
    ]
    beyond = [
        BeyondContrib(
            id=b["id"],
            title=b["title"],
            intro_html=b["intro_html"],
            entries=[_entry(e) for e in b.get("entries", [])],
            snippets=[_snip(s) for s in b.get("snippets", [])],
            notes_html=b.get("notes_html", ""),
            chapter=b.get("chapter", ""),
        )
        for b in payload.get("beyond", [])
    ]
    gaps = [GapEntry(**g) for g in payload.get("gaps", [])]
    aa = payload.get("axiom_anchors") or {"regression": "", "headlines": []}
    bm = payload.get("build_meta") or {"commit": "", "built_at": "", "auditor_lines": 0}
    return Document(
        preamble_html=payload.get("preamble_html", ""),
        sections=sections,
        chapters=chapters,
        beyond=beyond,
        gaps=gaps,
        verify_instructions_html=payload.get("verify_instructions_html", ""),
        axiom_anchors=AxiomAnchors(**aa),
        build_meta=BuildMeta(**bm),
    )
