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
It also carries the entry's cited Rocq ``idents`` and source ``files``,
which the client's search box matches against (searching by lemma name
is how a reader who knows the Rocq source finds the documentation entry)
and its info panel displays.  Group nodes carry ``n_entries`` so a
*collapsed* group can show its size without the client walking the node
list.

THE ARCHITECTURAL LANE
======================
``theories/`` is stratified into CI-enforced import layers (see
:mod:`tools.check_layers`), and that stratification — foundations →
measurable → linear ∥ stable → exponential → CBV → PPL — is the real
spatial story of the development.  Free-form graph layout hides it: the
same relation drawn by a force/rank layout puts a prelude lemma next to
a PPL theorem whenever an edge happens to be short.

So every entry node also carries the layer it belongs to, derived HERE
(not in the client) from the ``theories/<dir>/…`` paths already in
``files``:

* ``lane`` / ``lane_id`` — the swim-lane column (0 = Foundations …
  5 = PPL), the entry's layer being the **max** over its source files;
* ``band`` / ``band_id`` — the sub-band inside that lane.  A lane whose
  layer holds two *parallel* directories (``homs`` ∥ ``stable``,
  ``kernels`` ∥ ``exp`` — neither may import the other) has two bands,
  drawn stacked, which is how the picture says "these are independent";
* ``layer_dir`` — the ``theories/`` directory that decided it, and
  ``lane_src`` — ``files`` (derived from source paths), ``section``
  (no file info: inherited from the section's dominant lane) or
  ``fallback``, so the client (and a reader) can tell a measured lane
  from an inherited one;
* ``leaf`` / ``root`` — no *dependent* / no *dependency* in the full
  cross-tab ``depends`` relation.  Leaves are the headline results
  nothing else builds on; roots are the entries that build on nothing.

``meta["lanes"]`` describes the lane/band table itself (titles, member
directories) so captions are data, not client-side literals, and
``meta["lanes_by_tab"]`` sizes each lane per tab.

All of those are **additive**: the historical
``id``/``label``/``ntype``/``tab``/``parent``/``url``/``kind``/``status``
shape is unchanged, so an older client keeps working against a newer
``graph.json``.
"""

from __future__ import annotations

from collections import Counter
from pathlib import Path, PurePosixPath
from typing import Any

from .glob_deps import GlobRelation, build_glob_relation
from .schema import ALL_TABS, Document, Entry, ThreeTabDocument
from .xref import build_entry_edges

# ---------------------------------------------------------------------------
# The architectural lanes
# ---------------------------------------------------------------------------
#: The import layers of ``theories/``, in dependency order.  This MIRRORS
#: ``LAYERS`` in :mod:`tools.check_layers` (the CI-enforced checker) and is
#: duplicated rather than imported so ``graph.py`` keeps working when the
#: auditor package is vendored on its own; ``test_graph.py`` asserts the two
#: tables name exactly the same directories, so a new ``theories/`` directory
#: cannot appear in one and not the other.
LAYER_DIRS: tuple[tuple[str, ...], ...] = (
    ("prelude",),
    ("cones",),
    ("mcones",),
    ("icones",),
    ("homs", "stable"),
    ("kernels", "exp"),
    ("cbv",),
    ("programs",),
)

#: The swim-lanes the graph draws, left → right in dependency order.  A lane
#: groups the layers a reader thinks of as one architectural stage; a lane
#: with two BANDS is one whose layer holds two *parallel* directories —
#: ``homs`` never imports ``stable`` and vice versa — and the two bands are
#: drawn stacked to say exactly that.
LANES: tuple[dict[str, Any], ...] = (
    {
        "id": "foundations",
        "title": "Foundations",
        "subtitle": "prelude · cones",
        "bands": ({"id": "foundations", "title": "", "dirs": ("prelude", "cones")},),
    },
    {
        "id": "measurable",
        "title": "Measurable",
        "subtitle": "mcones · icones",
        "bands": ({"id": "measurable", "title": "", "dirs": ("mcones", "icones")},),
    },
    {
        "id": "linear-stable",
        "title": "Linear + Stable",
        "subtitle": "homs ∥ stable — parallel, neither imports the other",
        "bands": (
            {"id": "homs", "title": "Linear — homs, SMCC", "dirs": ("homs",)},
            {"id": "stable", "title": "Stable — scones", "dirs": ("stable",)},
        ),
    },
    {
        "id": "exponential",
        "title": "Exponential",
        "subtitle": "kernels ∥ exp — parallel",
        "bands": (
            {"id": "kernels", "title": "Kernels — s-finite", "dirs": ("kernels",)},
            {"id": "exp", "title": "Exponential — !, Seely", "dirs": ("exp",)},
        ),
    },
    {
        "id": "cbv",
        "title": "CBV",
        "subtitle": "cbv — Eilenberg–Moore, CBV leaves",
        "bands": ({"id": "cbv", "title": "", "dirs": ("cbv",)},),
    },
    {
        "id": "ppl",
        "title": "PPL",
        "subtitle": "programs — the language layer",
        "bands": ({"id": "ppl", "title": "", "dirs": ("programs",)},),
    },
)

#: ``theories/`` directory -> its layer rank (lower = closer to the base).
DIR_RANK: dict[str, int] = {
    d: i for i, dirs in enumerate(LAYER_DIRS) for d in dirs
}
#: ``theories/`` directory -> its position inside its own (parallel) layer,
#: which breaks ties deterministically when one entry cites files from two
#: parallel directories at the same rank.
DIR_SLOT: dict[str, int] = {
    d: j for dirs in LAYER_DIRS for j, d in enumerate(dirs)
}
#: ``theories/`` directory -> ``(lane index, band index)``.
DIR_LANE: dict[str, tuple[int, int]] = {
    d: (li, bi)
    for li, lane in enumerate(LANES)
    for bi, band in enumerate(lane["bands"])
    for d in band["dirs"]
}


def _layer_dir_of_file(path: str) -> str | None:
    """The ``theories/`` directory a source path lives in, or ``None``.

    ``theories/homs/linhom.v`` -> ``homs``; a nested
    ``theories/programs/infra/x.v`` still answers ``programs`` (the layer is
    the top-level directory, exactly as :mod:`tools.check_layers` reads it).
    Paths outside a known layer directory answer ``None`` so the caller can
    fall back rather than invent a lane.
    """
    parts = [p for p in PurePosixPath(str(path or "")).parts if p not in ("/", ".")]
    if not parts:
        return None
    start = parts.index("theories") + 1 if "theories" in parts else 0
    if start >= len(parts) - 1:      # nothing left but the file name itself
        return None
    return parts[start] if parts[start] in DIR_RANK else None


def _layer_dir_of_files(files) -> str | None:
    """The layer directory of an entry: the **max** layer over its files.

    An entry documenting both ``theories/cones/precone.v`` and
    ``theories/homs/linhom.v`` belongs where its *last* ingredient does —
    everything below is already available there, so the max is the only
    choice that keeps dependencies flowing one way across the lanes.
    """
    best: tuple[int, int, str] | None = None
    for f in files or ():
        d = _layer_dir_of_file(f)
        if d is None:
            continue
        key = (DIR_RANK[d], -DIR_SLOT[d], d)
        if best is None or key > best:
            best = key
    return best[2] if best else None


def _lanes_of_files(files) -> set[int]:
    """Every LANE an entry's own files touch (not just the max one).

    :func:`_layer_dir_of_files` answers *where the entry is placed*; this
    answers *how many layers it actually spans*, which is what tells a
    backward edge caused by the max-layer placement rule apart from one
    caused by something else entirely (a contested identifier, say).  An
    entry whose files all live in one lane can never be mis-placed BY THE
    PLACEMENT RULE, so a backward edge into it has a different cause.
    """
    out: set[int] = set()
    for f in files or ():
        d = _layer_dir_of_file(f)
        if d is not None:
            out.add(DIR_LANE[d][0])
    return out


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


def _dedup(values) -> list[str]:
    """Order-preserving de-duplication of a string sequence."""
    seen: set[str] = set()
    out: list[str] = []
    for v in values:
        if v and v not in seen:
            seen.add(v)
            out.append(v)
    return out


def _entry_idents(entry: Entry) -> list[str]:
    """The Rocq identifiers this entry documents (search keys, deduped)."""
    return _dedup(entry.rocq_idents)


def _entry_files(entry: Entry) -> list[str]:
    """The distinct ``theories/*.v`` paths this entry documents."""
    return _dedup(f.path for f in entry.rocq_files)


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
    # Node-id -> its ``data`` dict, so the entry walk can back-fill the
    # ``n_entries`` size a *collapsed* group node displays as its badge.
    container: dict[str, dict[str, Any]] = {}

    tab_titles = {"paper": "Paper", "ppl": "PPL", "examples": "Examples"}

    def add_tab(tab: str) -> str:
        nid = _tab_node_id(tab)
        if nid not in seen_groups:
            seen_groups.add(nid)
            data = {
                "id": nid,
                "label": tab_titles.get(tab, tab.upper()),
                "ntype": "tab",
                "tab": tab,
                "n_entries": 0,
            }
            container[nid] = data
            nodes.append({"data": data})
        return nid

    def add_group(
        tab: str, group_id: str, title: str, *, kind: str
    ) -> str:
        nid = _group_node_id(tab, group_id)
        if nid not in seen_groups:
            seen_groups.add(nid)
            data = {
                "id": nid,
                "label": title or group_id,
                "ntype": "group",
                "tab": tab,
                "parent": add_tab(tab),
                "url": _group_url(tab, group_id, kind=kind),
                "gkind": kind,
                "n_entries": 0,
            }
            container[nid] = data
            nodes.append({"data": data})
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
        group = container.get(group_nid, {})
        group["n_entries"] = group.get("n_entries", 0) + 1
        tab_nid = _tab_node_id(tab)
        if tab_nid in container:
            container[tab_nid]["n_entries"] += 1
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
                    # -- additive: search keys + info-panel provenance ----
                    "idents": _entry_idents(entry),
                    "files": _entry_files(entry),
                    "group_label": group.get("label", ""),
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


def _assign_lanes(nodes: list[dict[str, Any]]) -> None:
    """Stamp every node with its architectural lane, in place.

    Three sources, in order of authority:

    1. **the sources** — an entry citing ``theories/<dir>/…`` files sits in
       the lane of the max layer over them (``lane_src == "files"``);
    2. **the section** — an entry with no file info inherits the dominant
       lane of its section, because a documentation section is written at
       one architectural level even when one of its entries forgot to name
       a file (``lane_src == "section"``);
    3. **Foundations** — nothing known at all (``lane_src == "fallback"``),
       which puts the node at the left edge where an unplaced node is
       obvious rather than silently mixed into a real lane.

    Group nodes take their entries' dominant lane so the legacy
    group-by-section view can colour/order by lane too.
    """
    entries = [n["data"] for n in nodes if n["data"]["ntype"] == "entry"]
    # (lane, band) tallies per group, for the inheritance step.
    per_group: dict[str, Counter] = {}

    for d in entries:
        dirname = _layer_dir_of_files(d.get("files"))
        if dirname is None:
            continue
        # How many lanes this entry's files span, kept so the backward-edge
        # tally can name the right cause instead of blaming them all on the
        # max-layer placement rule.
        d["lane_span"] = len(_lanes_of_files(d.get("files")))
        lane, band = DIR_LANE[dirname]
        d["lane"] = lane
        d["lane_id"] = LANES[lane]["id"]
        d["band"] = band
        d["band_id"] = LANES[lane]["bands"][band]["id"]
        d["layer_dir"] = dirname
        d["lane_src"] = "files"
        per_group.setdefault(d.get("parent", ""), Counter())[(lane, band)] += 1

    def dominant(counts: Counter) -> tuple[int, int] | None:
        if not counts:
            return None
        # Most members wins; ties go to the LATER lane (the deeper layer),
        # which keeps the fallback from dragging an entry left of something
        # it depends on.
        return max(counts.items(), key=lambda kv: (kv[1], kv[0]))[0]

    for d in entries:
        if "lane" in d:
            continue
        got = dominant(per_group.get(d.get("parent", ""), Counter()))
        lane, band = got if got else (0, 0)
        d["lane"] = lane
        d["lane_id"] = LANES[lane]["id"]
        d["band"] = band
        d["band_id"] = LANES[lane]["bands"][band]["id"]
        d["layer_dir"] = ""
        d["lane_src"] = "section" if got else "fallback"

    for n in nodes:
        d = n["data"]
        if d["ntype"] != "group":
            continue
        got = dominant(per_group.get(d["id"], Counter()))
        lane, band = got if got else (0, 0)
        d["lane"] = lane
        d["lane_id"] = LANES[lane]["id"]
        d["band"] = band


def _assign_leaf_root(
    nodes: list[dict[str, Any]], edges: list[dict[str, Any]]
) -> None:
    """Flag the sinks and sources of the full cross-tab ``depends`` relation.

    An edge ``A → B`` reads "A uses B", so an entry NOTHING points at is one
    nothing else builds on: a **leaf**, i.e. a headline result — the nodes
    the reader of a formalisation is looking for.  An entry that points at
    nothing is a **root**: it rests on no other documented entry.

    Only real proof dependencies count (prose co-references would make every
    entry that is merely *named* somewhere stop being a leaf), and the whole
    three-tab relation counts: a Paper theorem used only by a PPL example is
    not a leaf, even while the Paper tab is the one on screen.

    An entry that is BOTH is ``isolated``: it takes no part in the entry-level
    dependency relation at all (a standalone definition whose identifier no
    other documented entry cites).  It satisfies the letter of "leaf", but it
    is not a headline result, so it is flagged separately and the client draws
    it with the quiet root mark instead of the leaf flag.
    """
    used_by_someone: set[str] = set()
    uses_something: set[str] = set()
    for e in edges:
        d = e["data"]
        if d.get("kind") != "depends":
            continue
        uses_something.add(d["source"])
        used_by_someone.add(d["target"])
    for n in nodes:
        d = n["data"]
        if d["ntype"] != "entry":
            continue
        d["leaf"] = d["id"] not in used_by_someone
        d["root"] = d["id"] not in uses_something
        d["isolated"] = d["leaf"] and d["root"]


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
    _assign_lanes(nodes)

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

    _assign_leaf_root(nodes, edges)

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
    # Per-tab node accounting.  The client renders ONE tab at a time (a
    # readable DAG rather than a three-tab hairball), so it needs the size
    # of each tab up front to label the tab selector before that tab has
    # ever been built.
    nodes_by_tab: dict[str, dict[str, int]] = {
        t: {"entries": 0, "groups": 0} for t in ALL_TABS
    }
    for n in nodes:
        d = n["data"]
        bucket = nodes_by_tab.get(d.get("tab", ""))
        if bucket is None:
            continue
        if d["ntype"] == "entry":
            bucket["entries"] += 1
        elif d["ntype"] == "group":
            bucket["groups"] += 1
    # Per-tab lane histogram + leaf/root tallies.  The client sizes its lane
    # captions from these before laying anything out, and the legend quotes
    # them; both are one pass over the nodes here rather than three in the
    # browser.
    lanes_by_tab: dict[str, list[int]] = {
        t: [0] * len(LANES) for t in ALL_TABS
    }
    leaves_by_tab: dict[str, int] = {t: 0 for t in ALL_TABS}
    n_leaves = 0
    n_roots = 0
    n_isolated = 0
    n_leaf_results = 0
    for n in nodes:
        d = n["data"]
        if d["ntype"] != "entry":
            continue
        row = lanes_by_tab.get(d.get("tab", ""))
        if row is not None:
            row[d.get("lane", 0)] += 1
        if d.get("leaf"):
            n_leaves += 1
        if d.get("root"):
            n_roots += 1
        if d.get("isolated"):
            n_isolated += 1
        elif d.get("leaf"):
            # The flagged set: a leaf that actually sits on top of something.
            n_leaf_results += 1
            if d.get("tab", "") in leaves_by_tab:
                leaves_by_tab[d["tab"]] += 1
    # Honesty metric: a ``depends`` edge whose source sits in a lane LEFT of
    # its target contradicts the left→right reading.  Such edges are FLAGGED
    # on the edge itself (``backward``) so the canvas can draw them as the
    # exceptions they are, and split by cause rather than lumped under one
    # explanation:
    #
    #   * ``multilayer``  — the target documents files from several layers and
    #     the max-layer rule placed it right of a dependency it only partly
    #     owns.  The placement rule is the cause and the picture is honest.
    #   * ``contested``   — the target's files all live in ONE layer, so the
    #     placement rule cannot be at fault.  These come from identifier
    #     ownership: an entry claims an ident that is defined (or heavily
    #     re-used) in another layer, and every use of it is then attributed to
    #     the claiming entry.  A data bug, surfaced by the lane view.
    node_lane = {
        n["data"]["id"]: n["data"].get("lane")
        for n in nodes
        if n["data"]["ntype"] == "entry"
    }
    node_span = {
        n["data"]["id"]: n["data"].get("lane_span", 0)
        for n in nodes
        if n["data"]["ntype"] == "entry"
    }
    n_backward = 0
    n_backward_multilayer = 0
    n_backward_contested = 0
    for e in edges:
        d = e["data"]
        if d["kind"] != "depends":
            continue
        s_lane = node_lane.get(d["source"])
        t_lane = node_lane.get(d["target"])
        if s_lane is not None and t_lane is not None and s_lane < t_lane:
            n_backward += 1
            d["backward"] = True
            if node_span.get(d["target"], 0) > 1:
                n_backward_multilayer += 1
            else:
                n_backward_contested += 1
    lane_meta = [
        {
            "index": i,
            "id": lane["id"],
            "title": lane["title"],
            "subtitle": lane["subtitle"],
            "bands": [
                {
                    "index": j,
                    "id": band["id"],
                    "title": band["title"],
                    "dirs": list(band["dirs"]),
                }
                for j, band in enumerate(lane["bands"])
            ],
        }
        for i, lane in enumerate(LANES)
    ]
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
            "nodes_by_tab": nodes_by_tab,
            # -- architectural lanes (additive) ---------------------------
            "lanes": lane_meta,
            "lanes_by_tab": lanes_by_tab,
            "n_leaves": n_leaves,
            "n_roots": n_roots,
            "n_isolated": n_isolated,
            "n_leaf_results": n_leaf_results,
            "leaves_by_tab": leaves_by_tab,
            "n_lane_backward": n_backward,
            "n_lane_backward_multilayer": n_backward_multilayer,
            "n_lane_backward_contested": n_backward_contested,
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


__all__ = ["LANES", "LAYER_DIRS", "build_graph"]
