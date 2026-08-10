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

from pathlib import Path
from typing import Any

from .glob_deps import GlobRelation, build_glob_relation
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

    def add_entry(
        tab: str, entry: Entry, group_nid: str, *, canonical: bool = False
    ) -> None:
        nid = _entry_node_id(tab, entry.id)
        if nid in seen_entries:
            return
        seen_entries.add(nid)
        entry_keys.add((tab, entry.id))
        # A collapsed single-entry section (id == section.id) has no
        # standalone entry page; its node links to the canonical section
        # page instead (mirrors xref.page_suffix / render's page skip).
        url = (
            f"{tab}/sections/{entry.id}.html"
            if canonical
            else _entry_url(tab, entry.id)
        )
        nodes.append(
            {
                "data": {
                    "id": nid,
                    "label": _short_label(entry),
                    "ntype": "entry",
                    "tab": tab,
                    "parent": group_nid,
                    "url": url,
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
            canonical = (
                len(section.entries) == 1
                and section.entries[0].id == section.id
            )
            for entry in section.entries:
                add_entry(tab, entry, gid, canonical=canonical)
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
                canonical = (
                    len(section.entries) == 1
                    and section.entries[0].id == section.id
                )
                for entry in section.entries:
                    add_entry(tab, entry, gid, canonical=canonical)
        # Paper Beyond contributions (entries not reachable via sections).
        # On PPL/Examples ``beyond`` aliases the chapter-tree entries, which
        # are already added above (dedup by node id makes this a no-op).
        for contrib in doc.beyond:
            gid = add_group(tab, contrib.id, contrib.title, kind="beyond")
            for entry in contrib.entries:
                add_entry(tab, entry, gid)

    return nodes, entry_keys


def build_graph(
    three: ThreeTabDocument,
    *,
    theories_root: str | Path | None = None,
    glob_relation: GlobRelation | None = None,
) -> dict[str, Any]:
    """Assemble the ``graph.json`` payload (nodes + edges + meta).

    * ``nodes`` — one per entry, plus group (section/contribution) and tab
      compound parents, each ``{data: {...}}`` in Cytoscape.js shape.
    * ``edges`` — deduped directed dependency edges between entry nodes,
      ``{data: {source, target, kind}}`` (self-edges already dropped
      upstream).  Two kinds are emitted:

      - ``depends`` — a **real Coq proof-level dependency** read from the
        ``.glob`` files (entry ``A``'s documented lemma *uses* an identifier
        that entry ``B`` documents).  These are the load-bearing edges and
        are styled solid in the client.
      - ``mentions`` — a **doc co-reference** (``A``'s statement/prose/snippet
        text names an identifier ``B`` documents).  Styled dashed/lighter.

      When the same ordered pair is both a real dependency and a doc mention
      it is emitted once as ``depends`` (the stronger relation wins).

    * ``meta`` — counts for the build log / tests (including per-kind edge
      counts and any graceful-degradation ``notices``).

    ``theories_root`` points at the ``theories/`` directory so the ``.glob``
    files can be located next to the ``.v`` sources.  Pass ``glob_relation``
    instead when the caller already computed it (the renderer does, so the
    ``.glob`` tree is parsed once for both the graph and the per-entry
    "Uses / Used by" navigation panels); it takes precedence over
    ``theories_root``.

    When neither is given (or no ``.glob`` is found) the ``depends`` edges
    degrade to empty and a NOTICE is recorded in ``meta["notices"]`` —
    :func:`build_graph` itself never fails.  Whether that degradation is
    *acceptable* is a build-policy question answered one level up, by the
    strict guard in :func:`tools.auditor.render.render`, using the
    ``glob_expected`` / ``n_glob_files`` provenance this function reports in
    ``meta``.

    Edges whose source or target is not a node (defensive; should not
    happen given both derive from the same entry walk) are filtered out so
    the client never references a dangling id.
    """
    nodes, entry_keys = _collect_nodes(three)

    # Real Coq proof dependencies (.glob) and doc co-references (text).
    rel = (
        glob_relation
        if glob_relation is not None
        else build_glob_relation(three, theories_root)
    )
    depends_raw = rel.edges
    notices = list(rel.notices)
    mentions_raw = build_entry_edges(three)

    edges: list[dict[str, Any]] = []
    edge_kind: dict[tuple[str, str], str] = {}

    def _emit(raw, kind: str) -> None:
        for (s_tab, s_id), (t_tab, t_id) in raw:
            if (s_tab, s_id) not in entry_keys or (t_tab, t_id) not in entry_keys:
                continue
            src = _entry_node_id(s_tab, s_id)
            tgt = _entry_node_id(t_tab, t_id)
            key = (src, tgt)
            prev = edge_kind.get(key)
            if prev == "depends":
                continue  # depends already wins for this pair
            edge_kind[key] = kind if prev is None else "depends"

    # Order matters only for which kind "wins"; the merge above makes the
    # result order-independent (depends always beats mentions).
    _emit(depends_raw, "depends")
    _emit(mentions_raw, "mentions")

    for (src, tgt), kind in sorted(edge_kind.items()):
        edges.append(
            {
                "data": {
                    "id": f"e{len(edges)}",
                    "source": src,
                    "target": tgt,
                    "kind": kind,
                }
            }
        )

    n_entry = sum(1 for n in nodes if n["data"]["ntype"] == "entry")
    n_group = sum(1 for n in nodes if n["data"]["ntype"] == "group")
    n_tab = sum(1 for n in nodes if n["data"]["ntype"] == "tab")
    n_depends = sum(1 for e in edges if e["data"]["kind"] == "depends")
    n_mentions = sum(1 for e in edges if e["data"]["kind"] == "mentions")
    # Per-tab edge accounting (an edge is counted for the tab that OWNS its
    # source entry; cross-tab edges are also totalled separately).  Cheap to
    # compute here and the only place that knows both endpoints' tabs.
    node_tab = {n["data"]["id"]: n["data"].get("tab", "") for n in nodes}
    by_tab: dict[str, dict[str, int]] = {
        t: {"depends": 0, "mentions": 0} for t in ALL_TABS
    }
    n_cross_tab = 0
    for e in edges:
        d = e["data"]
        s_tab = node_tab.get(d["source"], "")
        if s_tab in by_tab:
            by_tab[s_tab][d["kind"]] += 1
        if s_tab != node_tab.get(d["target"], ""):
            n_cross_tab += 1
    return {
        "nodes": nodes,
        "edges": edges,
        "meta": {
            "n_nodes": len(nodes),
            "n_entries": n_entry,
            "n_groups": n_group,
            "n_tabs": n_tab,
            "n_edges": len(edges),
            "n_depends": n_depends,
            "n_mentions": n_mentions,
            "n_cross_tab": n_cross_tab,
            "edges_by_tab": by_tab,
            # -- .glob provenance, consumed by the strict build guard ------
            "glob_expected": rel.expected,
            "glob_available": rel.available,
            "n_vfiles": rel.n_vfiles,
            "n_glob_files": rel.n_glob_found,
            "n_glob_missing": rel.n_glob_missing,
            "n_glob_objects": rel.n_objects,
            "notices": notices,
        },
    }


__all__ = ["build_graph"]
