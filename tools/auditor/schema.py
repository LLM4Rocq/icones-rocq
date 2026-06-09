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
    """A reference from one entry / section to another piece of content."""

    kind: str  # "section" | "entry" | "beyond" | "blueprint"
    target: str
    label: str


@dataclass
class CoqSnippet:
    """A Pygments-highlighted Coq code block."""

    source_file: str
    source_section: str | None
    highlighted_html: str  # Pygments output, language=coq


@dataclass
class NoteBlock:
    """A blockquote / aside paragraph attached to an entry's detail."""

    kind: str  # "note" | "warning" | "info"
    html: str


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
    """A paper-§ H2 section (e.g. "§ 2 — Cones")."""

    id: str
    paper_section: str
    paper_section_number: str
    title: str
    intro_html: str
    entries: list[Entry] = field(default_factory=list)
    notes_html: str = ""


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
        return CrossRef(**xr)

    def _snip(s: dict[str, Any]) -> CoqSnippet:
        return CoqSnippet(**s)

    def _note(n: dict[str, Any]) -> NoteBlock:
        return NoteBlock(**n)

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

    sections = [
        Section(
            id=s["id"],
            paper_section=s["paper_section"],
            paper_section_number=s["paper_section_number"],
            title=s["title"],
            intro_html=s["intro_html"],
            entries=[_entry(e) for e in s.get("entries", [])],
            notes_html=s.get("notes_html", ""),
        )
        for s in payload.get("sections", [])
    ]
    beyond = [
        BeyondContrib(
            id=b["id"],
            title=b["title"],
            intro_html=b["intro_html"],
            entries=[_entry(e) for e in b.get("entries", [])],
            snippets=[_snip(s) for s in b.get("snippets", [])],
            notes_html=b.get("notes_html", ""),
        )
        for b in payload.get("beyond", [])
    ]
    gaps = [GapEntry(**g) for g in payload.get("gaps", [])]
    aa = payload.get("axiom_anchors") or {"regression": "", "headlines": []}
    bm = payload.get("build_meta") or {"commit": "", "built_at": "", "auditor_lines": 0}
    return Document(
        preamble_html=payload.get("preamble_html", ""),
        sections=sections,
        beyond=beyond,
        gaps=gaps,
        verify_instructions_html=payload.get("verify_instructions_html", ""),
        axiom_anchors=AxiomAnchors(**aa),
        build_meta=BuildMeta(**bm),
    )
