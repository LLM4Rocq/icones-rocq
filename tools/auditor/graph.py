"""Build the interactive dependency-graph data emitted as ``graph.json``.

The graph turns the auditor's existing cross-reference relation into a
navigable, clickable map of the formalisation.  Two things are reused
wholesale from :mod:`tools.auditor.xref`:

* **the dependency edges** — :func:`~tools.auditor.xref.build_entry_edges`
  yields one directed edge ``A -> B`` whenever entry ``A``'s code/prose
  mentions an identifier *owned* by another entry ``B`` (the very relation
  the snippet/prose linkifier uses to turn an ident into a link to its
  definer), cross-tab aware; and
* **the hierarchy** — the parsed :class:`~tools.auditor.schema.Document`
  tree: a tab owns chapters/sections, a section owns entries.  We emit a
  *compound* node graph (Cytoscape.js parent/child nesting): every entry
  node has a ``parent`` section/contrib group, every group has a ``parent``
  tab group.  The renderer colours by tab and boxes by group, so the
  Paper §2→§9 / PPL chapters / Examples chapters structure is visible at a
  glance.

Node-id scheme (collision-free across tabs):

* entry nodes:  ``<tab>::<entry_id>``
* group nodes:  ``grp::<tab>::<group_id>`` (a Paper §-section, a Paper
  Beyond contribution, or a PPL/Examples H3 section)
* tab nodes:    ``tab::<tab>``

Every entry node carries a ``url`` relative to the graph page
(``<tab>/entries/<id>.html``), the parent group's id+title, the owning
tab, the entry ``kind`` (Def/Thm/…) and its ``status`` list, so the
client can render, colour, filter and navigate without a second fetch.
"""

from __future__ import annotations

from typing import Any

from .schema import ALL_TABS, Document, Entry, ThreeTabDocument
from .xref import build_entry_edges


def _entry_node_id(tab: str, entry_id: str) -> str:
    return f"{tab}::{entry_id}"


def _group_node_id(tab: str, group_id: str) -> str:
    return f"grp::{tab}::{group_id}"


def _tab_node_id(tab: str) -> str:
    return f"tab::{tab}"


def _entry_url(tab: str, entry_id: str) -> str:
    """URL of an entry page relative to the depth-0 graph page."""
    return f"{tab}/entries/{entry_id}.html"


#: Route segment per group kind, mirroring the per-tab page tree emitted by
#: :func:`tools.auditor.render._emit_tab` (``sections/``, ``chapters/`` are
#: pluralised; ``beyond/`` is not).
_GROUP_ROUTE = {"section": "sections", "chapter": "chapters", "beyond": "beyond"}


def _group_url(tab: str, group_id: str, *, kind: str) -> str:
    """URL of a group page relative to the depth-0 graph page.

    ``kind`` is ``"section"``, ``"chapter"`` or ``"beyond"`` — the route
    segment mirrors :func:`tools.auditor.render._emit_tab`'s page tree.
    """
    return f"{tab}/{_GROUP_ROUTE[kind]}/{group_id}.html"


def _short_label(entry: Entry) -> str:
    """A compact node label: the paper label (``Def 2.1``, ``thm-6-5``)."""
    return entry.paper_label or entry.id


def _collect_nodes(
    three: ThreeTabDocument,
) -> tuple[list[dict[str, Any]], set[tuple[str, str]]]:
    """Build the node list (tabs, groups, entries) and the known-entry set.

    Returns ``(nodes, entry_keys)`` where ``entry_keys`` is the set of
    ``(tab, entry_id)`` pairs that became entry nodes — used to validate
    edges against the node set.
    """
    nodes: list[dict[str, Any]] = []
    entry_keys: set[tuple[str, str]] = set()
    seen_groups: set[str] = set()
    seen_entries: set[str] = set()

    tab_titles = {"paper": "Paper", "ppl": "PPL", "examples": "Examples"}

    def add_tab(tab: str) -> str:
        nid = _tab_node_id(tab)
        if nid not in seen_groups:
            seen_groups.add(nid)
            nodes.append(
                {
                    "data": {
                        "id": nid,
                        "label": tab_titles.get(tab, tab.upper()),
                        "ntype": "tab",
                        "tab": tab,
                    }
                }
            )
        return nid

    def add_group(
        tab: str, group_id: str, title: str, *, kind: str
    ) -> str:
        nid = _group_node_id(tab, group_id)
        if nid not in seen_groups:
            seen_groups.add(nid)
            nodes.append(
                {
                    "data": {
                        "id": nid,
                        "label": title or group_id,
                        "ntype": "group",
                        "tab": tab,
                        "parent": add_tab(tab),
                        "url": _group_url(tab, group_id, kind=kind),
                    }
                }
            )
        return nid

    def add_entry(tab: str, entry: Entry, group_nid: str) -> None:
        nid = _entry_node_id(tab, entry.id)
        if nid in seen_entries:
            return
        seen_entries.add(nid)
        entry_keys.add((tab, entry.id))
        nodes.append(
            {
                "data": {
                    "id": nid,
                    "label": _short_label(entry),
                    "ntype": "entry",
                    "tab": tab,
                    "parent": group_nid,
                    "url": _entry_url(tab, entry.id),
                    "kind": entry.paper_kind,
                    "status": list(entry.status),
                }
            }
        )

    for tab in ALL_TABS:
        doc: Document = three.tab(tab)
        # Paper-style §-section tree (Paper tab).
        for section in doc.sections:
            gid = add_group(
                tab, section.id, section.paper_section or section.title,
                kind="section",
            )
            for entry in section.entries:
                add_entry(tab, entry, gid)
        # PPL/Examples chapter -> section tree.  We nest under the *section*
        # group (one hierarchy level the client can collapse); chapters are
        # carried as the section's chapter title for optional grouping but
        # the compound parent stays at section level to keep nesting shallow
        # and readable.
        for chapter in doc.chapters:
            for section in chapter.sections:
                gid = add_group(
                    tab, section.id, section.title or section.id,
                    kind="section",
                )
                for entry in section.entries:
                    add_entry(tab, entry, gid)
        # Paper Beyond contributions (entries not reachable via sections).
        # On PPL/Examples ``beyond`` aliases the chapter-tree entries, which
        # are already added above (dedup by node id makes this a no-op).
        for contrib in doc.beyond:
            gid = add_group(tab, contrib.id, contrib.title, kind="beyond")
            for entry in contrib.entries:
                add_entry(tab, entry, gid)

    return nodes, entry_keys


def build_graph(three: ThreeTabDocument) -> dict[str, Any]:
    """Assemble the ``graph.json`` payload (nodes + edges + meta).

    * ``nodes`` — one per entry, plus group (section/contribution) and tab
      compound parents, each ``{data: {...}}`` in Cytoscape.js shape.
    * ``edges`` — deduped directed dependency edges between entry nodes,
      ``{data: {source, target}}`` (self-edges already dropped upstream).
    * ``meta`` — counts for the build log / tests.

    Edges whose source or target is not a node (defensive; should not
    happen given both derive from the same entry walk) are filtered out so
    the client never references a dangling id.
    """
    nodes, entry_keys = _collect_nodes(three)

    raw_edges = build_entry_edges(three)
    edges: list[dict[str, Any]] = []
    seen_edge: set[tuple[str, str]] = set()
    for (s_tab, s_id), (t_tab, t_id) in raw_edges:
        if (s_tab, s_id) not in entry_keys or (t_tab, t_id) not in entry_keys:
            continue
        src = _entry_node_id(s_tab, s_id)
        tgt = _entry_node_id(t_tab, t_id)
        key = (src, tgt)
        if key in seen_edge:
            continue
        seen_edge.add(key)
        edges.append({"data": {"id": f"e{len(edges)}", "source": src, "target": tgt}})

    n_entry = sum(1 for n in nodes if n["data"]["ntype"] == "entry")
    n_group = sum(1 for n in nodes if n["data"]["ntype"] == "group")
    n_tab = sum(1 for n in nodes if n["data"]["ntype"] == "tab")
    return {
        "nodes": nodes,
        "edges": edges,
        "meta": {
            "n_nodes": len(nodes),
            "n_entries": n_entry,
            "n_groups": n_group,
            "n_tabs": n_tab,
            "n_edges": len(edges),
        },
    }


__all__ = ["build_graph"]
