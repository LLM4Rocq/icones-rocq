"""Build the global table-of-contents tree for the sidebar navigation.

The sidebar shows the FULL site hierarchy on every page so a reader can
jump anywhere without going back to an index.  The tree is built once per
build from the three parsed :class:`~tools.auditor.schema.Document` tabs
and injected (identically) into every page's template context; only the
"active" highlight differs per page, which the template computes from the
current ``(tab, kind, id)`` triple.

Tree shape (each node a plain dict, JSON-friendly and Jinja-friendly):

    tab            tab → (chapter →)? group → entry
      chapter      PPL / Examples only (H2 chapters)
        group      a Paper §-section, a Paper Beyond contribution, or a
                   PPL/Examples H3 section
          entry    a single paper-statement ↔ Rocq-identifier row

Every node carries::

    {
      "kind":  "tab" | "chapter" | "section" | "beyond" | "entry",
      "id":    str,                # node id (or tab slug for a tab node)
      "title": str,                # display label
      "url":   str | None,         # site-root-relative URL (no depth prefix)
      "children": [ ... ],
    }

``url`` is relative to the *site root* (``out/``); the template prepends
the page's ``tab_prefix`` (which always resolves to the site root from any
page depth) so links are correct from every page.  Tab nodes link to the
tab landing; group nodes to their section/beyond/chapter page; entry nodes
to the standalone entry page.
"""

from __future__ import annotations

from typing import Any

from .schema import (
    TAB_EXAMPLES,
    TAB_PAPER,
    TAB_PPL,
    Document,
    ThreeTabDocument,
)


#: Human label shown for each tab group at the top level of the sidebar.
_TAB_LABELS = {
    TAB_PAPER: "Paper",
    TAB_PPL: "PPL",
    TAB_EXAMPLES: "Examples",
}


def _entry_node(tab: str, entry: Any) -> dict[str, Any]:
    return {
        "kind": "entry",
        "id": entry.id,
        "title": entry.paper_label or entry.id,
        "url": f"{tab}/entries/{entry.id}.html",
        "children": [],
    }


def _section_node(tab: str, section: Any) -> dict[str, Any]:
    label = section.title or section.id
    if getattr(section, "paper_section_number", ""):
        label = f"§ {section.paper_section_number} — {label}"
    # A PPL/Examples H3 becomes a Section wrapping ONE synthetic entry whose
    # id == section.id.  That entry has no standalone page (the section page
    # is canonical and inlines it), so we drop the identical entry child:
    # one node, no duplicate link in the sidebar.  Multi-entry sections keep
    # their entry children.
    entries = section.entries
    canonical = len(entries) == 1 and entries[0].id == section.id
    children = [] if canonical else [_entry_node(tab, e) for e in entries]
    return {
        "kind": "section",
        "id": section.id,
        "title": label,
        "url": f"{tab}/sections/{section.id}.html",
        "children": children,
    }


def _beyond_node(tab: str, contrib: Any) -> dict[str, Any]:
    return {
        "kind": "beyond",
        "id": contrib.id,
        "title": contrib.title or contrib.id,
        "url": f"{tab}/beyond/{contrib.id}.html",
        "children": [_entry_node(tab, e) for e in contrib.entries],
    }


def _chapter_node(tab: str, chapter: Any) -> dict[str, Any]:
    return {
        "kind": "chapter",
        "id": chapter.id,
        "title": chapter.title or chapter.id,
        "url": f"{tab}/chapters/{chapter.id}.html",
        "children": [_section_node(tab, s) for s in chapter.sections],
    }


def _tab_node(tab: str, doc: Document) -> dict[str, Any]:
    """Build the sub-tree for one tab.

    PPL / Examples use the chapter tree (``doc.chapters``); the Paper tab
    uses ``doc.sections`` plus its Beyond contributions (mirroring how
    :func:`tools.auditor.render._emit_tab` decides which page tree to emit).
    """
    children: list[dict[str, Any]] = []
    if doc.chapters:
        children.extend(_chapter_node(tab, c) for c in doc.chapters)
    else:
        children.extend(_section_node(tab, s) for s in doc.sections)
        children.extend(_beyond_node(tab, b) for b in doc.beyond)
    return {
        "kind": "tab",
        "id": tab,
        "title": _TAB_LABELS.get(tab, tab.upper()),
        "url": f"{tab}/index.html",
        "children": children,
    }


def build_toc(doc: ThreeTabDocument) -> list[dict[str, Any]]:
    """Build the ordered global TOC tree (one node per tab, in tab order).

    Returns a list of three tab nodes (Paper, PPL, Examples).  The result
    is the SAME on every page; the active highlight is computed per page in
    the template from the current ``(tab, kind, id)``.
    """
    return [
        _tab_node(TAB_PAPER, doc.paper),
        _tab_node(TAB_PPL, doc.ppl),
        _tab_node(TAB_EXAMPLES, doc.examples),
    ]
