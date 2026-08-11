"""Tests for the dependency-graph data emission (``tools.auditor.graph``).

The graph reuses the xref relation (entry A references an identifier owned
by entry B ⇒ edge A→B) and the parsed Document hierarchy (tab → group →
entry compound nesting).  These tests check the emitted data is well
formed: every edge endpoint is a real node, no self-edges, parents resolve,
entry URLs follow the page route, and the hierarchy is carried.

They also pin the ARCHITECTURAL LANE the client lays the graph out on: an
entry's lane is derived here, in Python, from the ``theories/<dir>/…``
paths it documents, following the same layer table the CI import checker
enforces — including the parallel ``homs`` ∥ ``stable`` pair that shares one
lane as two stacked bands — plus the leaf/root flags that mark the sinks and
sources of the real dependency relation.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT.parent) not in sys.path:
    sys.path.insert(0, str(ROOT.parent))

from tools.auditor.glob_deps import GlobRelation, build_glob_edges, parse_glob_uses
from tools.auditor.graph import build_graph
from tools.auditor.schema import (
    CoqSnippet,
    Document,
    Entry,
    EntryDetail,
    RocqFile,
    Section,
    ThreeTabDocument,
)
from tools.auditor.xref import build_entry_edges


def _name_span(ident: str) -> str:
    return f'<span class="n">{ident}</span>'


def _entry(eid: str, idents, snippet_html: str = "", vfile="") -> Entry:
    vfiles = [vfile] if isinstance(vfile, str) else list(vfile)
    vfiles = [v for v in vfiles if v]
    return Entry(
        id=eid,
        paper_label=eid,
        paper_kind="Def",
        paper_number=None,
        paper_section_id="sec-x",
        statement_html="",
        rocq_idents=list(idents),
        rocq_files=[
            RocqFile(
                path=v,
                section=None,
                github_url="",
                coqdoc_url=None,
                coqdoc_anchor=None,
            )
            for v in vfiles
        ],
        status=["axiom-free"],
        detail=EntryDetail(
            prose_html="",
            snippets=[
                CoqSnippet(
                    source_file="x.v",
                    source_section=None,
                    highlighted_html=snippet_html,
                )
            ],
        ),
    )


def _section(sid: str, entries) -> Section:
    return Section(
        id=sid,
        paper_section=f"§ {sid}",
        paper_section_number=sid,
        title=sid,
        intro_html="",
        entries=list(entries),
    )


def _three(*, paper=(), ppl=(), examples=()) -> ThreeTabDocument:
    def _doc(secs):
        d = Document(preamble_html="")
        d.sections = list(secs)
        return d

    return ThreeTabDocument(
        paper=_doc(paper), ppl=_doc(ppl), examples=_doc(examples)
    )


def _byid(graph):
    return {n["data"]["id"]: n["data"] for n in graph["nodes"]}


def test_edge_from_reference_to_definer():
    """B mentions A's ident ⇒ a directed edge B→A (and no self-edge)."""
    a = _entry("def-a", idents=["alpha_widget"], snippet_html="")
    b = _entry(
        "def-b", idents=["beta_widget"], snippet_html=_name_span("alpha_widget")
    )
    three = _three(paper=[_section("sec-x", [a, b])])

    edges = build_entry_edges(three)
    assert (("paper", "def-b"), ("paper", "def-a")) in edges
    # No self-edges even though each entry's snippet contains its own ident
    # nowhere here; assert defensively for the general property.
    assert all(s != t for s, t in edges)


def test_cross_tab_edge():
    """A PPL entry naming a Paper-owned ident yields ONE undirected edge.

    Text overlap is a co-reference, so the payload states a *pair*: one
    edge, ``directed: false``, endpoints in canonical order.  Asserting an
    orientation here would be asserting the very direction claim the panel
    and the canvas were fixed to stop making.
    """
    paper = _entry("thm-9-7", idents=["EM_term"], snippet_html="")
    ppl = _entry(
        "ppl-x", idents=["tyD_cbv"], snippet_html=_name_span("EM_term")
    )
    three = _three(paper=[_section("sec-x", [paper])], ppl=[_section("ppl-s", [ppl])])

    graph = build_graph(three)
    co = [e["data"] for e in graph["edges"] if e["data"]["kind"] == "mentions"]
    assert len(co) == 1
    assert {co[0]["source"], co[0]["target"]} == {"ppl::ppl-x", "paper::thm-9-7"}
    assert co[0]["directed"] is False


def test_mentions_are_undirected_and_deduped():
    """Two entries naming each other are ONE co-reference, not two arrows."""
    a = _entry("def-a", idents=["alpha_widget"], snippet_html=_name_span("beta_widget"))
    b = _entry("def-b", idents=["beta_widget"], snippet_html=_name_span("alpha_widget"))
    three = _three(paper=[_section("sec-x", [a, b])])

    graph = build_graph(three)
    co = [e["data"] for e in graph["edges"] if e["data"]["kind"] == "mentions"]
    assert len(co) == 1, [(e["source"], e["target"]) for e in co]
    # Canonical (sorted) orientation, so the record is unique rather than
    # a claim about which entry came first.
    assert (co[0]["source"], co[0]["target"]) == ("paper::def-a", "paper::def-b")


def test_a_proof_dependency_suppresses_the_co_reference_either_way():
    """The strong relation subsumes the weak one, in EITHER direction.

    Same rule the card panel applies, so the graph and the panel cannot
    disagree about a pair.
    """
    a = _entry("def-a", idents=["alpha_widget"], snippet_html=_name_span("beta_widget"))
    b = _entry("def-b", idents=["beta_widget"], snippet_html=_name_span("alpha_widget"))
    three = _three(paper=[_section("sec-x", [a, b])])
    rel = GlobRelation(edges=[(("paper", "def-a"), ("paper", "def-b"))])

    graph = build_graph(three, glob_relation=rel)
    kinds = [e["data"]["kind"] for e in graph["edges"]]
    assert kinds == ["depends"], [
        (e["data"]["source"], e["data"]["target"], e["data"]["kind"])
        for e in graph["edges"]
    ]


def test_graph_well_formed_no_dangling():
    """Every edge endpoint is a node; no self-edges; parents resolve."""
    a = _entry("def-a", idents=["alpha_widget"], snippet_html="")
    b = _entry(
        "def-b", idents=["beta_widget"], snippet_html=_name_span("alpha_widget")
    )
    three = _three(paper=[_section("sec-x", [a, b])])

    graph = build_graph(three)
    ids = set(_byid(graph))

    for e in graph["edges"]:
        assert e["data"]["source"] in ids
        assert e["data"]["target"] in ids
        assert e["data"]["source"] != e["data"]["target"]

    for n in graph["nodes"]:
        parent = n["data"].get("parent")
        if parent is not None:
            assert parent in ids


def test_graph_hierarchy_compound_parents():
    """Entry → group → tab compound nesting is emitted with correct ids."""
    a = _entry("def-a", idents=["alpha_widget"], snippet_html="")
    three = _three(paper=[_section("sec-x", [a])])

    graph = build_graph(three)
    byid = _byid(graph)

    assert "tab::paper" in byid and byid["tab::paper"]["ntype"] == "tab"
    assert "grp::paper::sec-x" in byid
    grp = byid["grp::paper::sec-x"]
    assert grp["ntype"] == "group" and grp["parent"] == "tab::paper"
    ent = byid["paper::def-a"]
    assert ent["ntype"] == "entry"
    assert ent["parent"] == "grp::paper::sec-x"
    assert ent["tab"] == "paper"
    assert ent["kind"] == "Def"
    assert ent["status"] == ["axiom-free"]


def test_entry_url_follows_route():
    """Entry node URLs are ``<tab>/entries/<id>.html`` (depth-0 relative)."""
    a = _entry("def-a", idents=["alpha_widget"], snippet_html="")
    three = _three(ppl=[_section("ppl-s", [a])])

    graph = build_graph(three)
    ent = _byid(graph)["ppl::def-a"]
    assert ent["url"] == "ppl/entries/def-a.html"
    grp = _byid(graph)["grp::ppl::ppl-s"]
    assert grp["url"] == "ppl/sections/ppl-s.html"


def test_entry_nodes_carry_search_keys_and_provenance():
    """Entry nodes carry their Rocq ``idents``/``files`` and section label.

    The graph page searches by *cited Rocq identifier* (that is how a reader
    who knows the source finds the documentation entry) and its info panel
    names the source file, so both have to travel in ``graph.json``: the
    client makes exactly one fetch and never sees the parsed Document.
    """
    a = _entry(
        "def-a",
        idents=["alpha_widget", "alpha_widget_ext", "alpha_widget"],
        vfile="theories/demo/alpha.v",
    )
    three = _three(paper=[_section("sec-x", [a])])

    ent = _byid(build_graph(three))["paper::def-a"]
    # Deduped, order preserving.
    assert ent["idents"] == ["alpha_widget", "alpha_widget_ext"]
    assert ent["files"] == ["theories/demo/alpha.v"]
    # The containing section's display label, for the info panel.
    assert ent["group_label"] == "§ sec-x"


def test_entry_without_sources_still_has_empty_search_keys():
    """The additive fields are always present (never missing keys)."""
    a = _entry("def-a", idents=[])
    three = _three(ppl=[_section("ppl-s", [a])])

    ent = _byid(build_graph(three))["ppl::def-a"]
    assert ent["idents"] == [] and ent["files"] == []


def test_group_and_tab_nodes_carry_entry_counts():
    """Collapsed group nodes need their size without walking the node list."""
    entries = [_entry(f"def-{i}", idents=[f"w{i}"]) for i in range(3)]
    three = _three(
        paper=[_section("sec-x", entries[:2]), _section("sec-y", entries[2:])]
    )

    byid = _byid(build_graph(three))
    assert byid["grp::paper::sec-x"]["n_entries"] == 2
    assert byid["grp::paper::sec-y"]["n_entries"] == 1
    assert byid["grp::paper::sec-x"]["gkind"] == "section"
    # The tab node totals its groups.
    assert byid["tab::paper"]["n_entries"] == 3


def test_node_shape_stays_backward_compatible():
    """The historical node keys are untouched — new fields are additive."""
    a = _entry("def-a", idents=["alpha_widget"], vfile="theories/demo/alpha.v")
    three = _three(paper=[_section("sec-x", [a])])

    byid = _byid(build_graph(three))
    for key in ("id", "label", "ntype", "tab", "parent", "url", "kind", "status"):
        assert key in byid["paper::def-a"], key
    for key in ("id", "label", "ntype", "tab", "parent", "url"):
        assert key in byid["grp::paper::sec-x"], key
    for key in ("id", "label", "ntype", "tab"):
        assert key in byid["tab::paper"], key


def test_meta_reports_nodes_per_tab():
    """The client renders one tab at a time and sizes the selector up front."""
    three = _three(
        paper=[_section("sec-x", [_entry("def-a", idents=["a_w"])])],
        ppl=[
            _section(
                "ppl-s",
                [_entry("ppl-a", idents=["p_w"]), _entry("ppl-b", idents=["q_w"])],
            )
        ],
    )

    meta = build_graph(three)["meta"]
    assert meta["nodes_by_tab"]["paper"] == {"entries": 1, "groups": 1}
    assert meta["nodes_by_tab"]["ppl"] == {"entries": 2, "groups": 1}
    assert meta["nodes_by_tab"]["examples"] == {"entries": 0, "groups": 0}
    # Totals stay consistent with the per-tab split.
    assert sum(v["entries"] for v in meta["nodes_by_tab"].values()) == (
        meta["n_entries"]
    )


def test_graph_page_caption_is_per_tab(tmp_path):
    """The hero caption sizes the TAB on screen, not the whole dataset.

    The canvas draws one tab at a time, so a caption quoting the three-tab
    entry total sat directly above a stats line reporting a single tab and
    contradicted it.  ``meta.nodes_by_tab`` is the per-tab split; the page
    must render the default (Paper) tab's numbers from it, keep the whole
    dataset figure clearly marked as such, and expose the ``cy-caption``
    hook graph.js re-states on every tab switch.
    """
    from tools.auditor.render import render

    three = _three(
        paper=[_section("sec-x", [_entry("def-a", idents=["a_w"])])],
        ppl=[
            _section(
                "ppl-s",
                [_entry("ppl-a", idents=["p_w"]), _entry("ppl-b", idents=["q_w"])],
            )
        ],
    )
    render(three, tmp_path / "site", require_glob_deps=False)
    raw = (tmp_path / "site" / "graph.html").read_text(encoding="utf-8")
    html = " ".join(raw.split())   # the template wraps; compare on one line

    assert 'id="cy-caption"' in html          # the per-tab hook graph.js owns
    assert "Paper tab: 1 entries in 1 sections" in html  # the tab, not the total
    # The dataset-wide total is still stated, but labelled as such.
    assert "All three tabs together: 3 entries in 2 sections" in html
    # Legend counts that describe the whole dataset say so.
    assert "entries across all tabs" in html


def test_meta_counts_consistent():
    """``meta`` counts match the emitted node/edge lists."""
    a = _entry("def-a", idents=["alpha_widget"], snippet_html="")
    b = _entry(
        "def-b", idents=["beta_widget"], snippet_html=_name_span("alpha_widget")
    )
    three = _three(paper=[_section("sec-x", [a, b])])

    graph = build_graph(three)
    meta = graph["meta"]
    assert meta["n_nodes"] == len(graph["nodes"])
    assert meta["n_edges"] == len(graph["edges"])
    assert meta["n_entries"] == 2
    assert meta["n_tabs"] == 1
    assert meta["n_groups"] == 1


# -- architectural lanes ----------------------------------------------------


def test_lane_table_matches_the_layer_checker():
    """The lane table names exactly the directories CI enforces layers for.

    ``graph.py`` keeps its own copy of the layer table (so the auditor stays
    vendorable on its own).  A copy that drifts is worse than no copy: a new
    ``theories/`` directory would be laid out at the left edge of the graph
    while ``check_layers.py`` happily ranks it.  This test is the join.
    """
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "_check_layers", ROOT / "check_layers.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    from tools.auditor.graph import LANES, LAYER_DIRS

    assert [list(t) for t in LAYER_DIRS] == [list(t) for t in mod.LAYERS]
    # Every layer directory lands in exactly one lane band, and every band
    # names only real directories.
    placed = [d for lane in LANES for band in lane["bands"] for d in band["dirs"]]
    assert sorted(placed) == sorted(mod.RANK)
    assert len(placed) == len(set(placed))
    # Lanes are ordered: a lane's directories never rank below an earlier
    # lane's, which is what makes "left → right" a dependency order.
    tops = [max(mod.RANK[d] for b in lane["bands"] for d in b["dirs"]) for lane in LANES]
    assert tops == sorted(tops)


def test_lane_assigned_from_source_file_path():
    """Each ``theories/<dir>/`` maps to its architectural lane and band."""
    cases = {
        "prelude": ("foundations", "foundations", 0, 0),
        "cones": ("foundations", "foundations", 0, 0),
        "mcones": ("measurable", "measurable", 1, 0),
        "icones": ("measurable", "measurable", 1, 0),
        "homs": ("linear-stable", "homs", 2, 0),
        "stable": ("linear-stable", "stable", 2, 1),
        "kernels": ("exponential", "kernels", 3, 0),
        "exp": ("exponential", "exp", 3, 1),
        "cbv": ("cbv", "cbv", 4, 0),
        "programs": ("ppl", "ppl", 5, 0),
    }
    entries = [
        _entry(f"def-{d}", idents=[f"w_{d}"], vfile=f"theories/{d}/mod.v")
        for d in cases
    ]
    byid = _byid(build_graph(_three(paper=[_section("sec-x", entries)])))

    for d, (lane_id, band_id, lane, band) in cases.items():
        node = byid[f"paper::def-{d}"]
        assert (node["lane_id"], node["band_id"]) == (lane_id, band_id), d
        assert (node["lane"], node["band"]) == (lane, band), d
        assert node["layer_dir"] == d
        assert node["lane_src"] == "files"


def test_parallel_directories_are_one_lane_in_two_bands():
    """``homs`` ∥ ``stable`` (and ``kernels`` ∥ ``exp``) share a lane.

    They are parallel layers — neither may import the other — so the picture
    must NOT put one to the left of the other, which would read as "stable
    is built on homs".  Same column, two stacked bands.
    """
    entries = [
        _entry("def-h", idents=["h_w"], vfile="theories/homs/linhom.v"),
        _entry("def-s", idents=["s_w"], vfile="theories/stable/scone.v"),
        _entry("def-k", idents=["k_w"], vfile="theories/kernels/sfin.v"),
        _entry("def-e", idents=["e_w"], vfile="theories/exp/bang.v"),
    ]
    byid = _byid(build_graph(_three(paper=[_section("sec-x", entries)])))
    h, s = byid["paper::def-h"], byid["paper::def-s"]
    k, e = byid["paper::def-k"], byid["paper::def-e"]

    assert h["lane"] == s["lane"] and h["band"] != s["band"]
    assert k["lane"] == e["lane"] and k["band"] != e["band"]
    # …and the two parallel lanes are still ordered against each other.
    assert h["lane"] < k["lane"]


def test_lane_is_the_max_layer_over_the_entry_files():
    """An entry spanning layers belongs to its DEEPEST one.

    Everything below a layer is available there, so taking the max is the
    only rule under which a dependency cannot point rightwards across the
    lanes.  (A tie between two parallel directories resolves to the first
    declared, so the answer never depends on file order.)
    """
    spanning = _entry(
        "thm-span",
        idents=["span_w"],
        vfile=["theories/cones/precone.v", "theories/homs/linhom.v"],
    )
    tie = _entry(
        "thm-tie",
        idents=["tie_w"],
        vfile=["theories/stable/scone.v", "theories/homs/linhom.v"],
    )
    byid = _byid(build_graph(_three(paper=[_section("sec-x", [spanning, tie])])))

    assert byid["paper::thm-span"]["layer_dir"] == "homs"
    assert byid["paper::thm-span"]["lane_id"] == "linear-stable"
    assert byid["paper::thm-tie"]["layer_dir"] == "homs"


def test_nested_and_unknown_source_paths():
    """A nested path keeps its top directory; an unknown one does not lie."""
    nested = _entry(
        "def-nested", idents=["n_w"], vfile="theories/programs/infra/util.v"
    )
    stray = _entry("def-stray", idents=["s_w"], vfile="theories/sandbox/toy.v")
    byid = _byid(
        build_graph(
            _three(
                paper=[_section("sec-a", [nested])],
                ppl=[_section("sec-b", [stray])],
            )
        )
    )
    assert byid["paper::def-nested"]["lane_id"] == "ppl"
    assert byid["paper::def-nested"]["layer_dir"] == "programs"
    # No known layer anywhere in the section ⇒ parked at the left edge and
    # flagged as such rather than silently placed in a real lane.
    assert byid["ppl::def-stray"]["lane"] == 0
    assert byid["ppl::def-stray"]["lane_src"] == "fallback"


def test_entry_without_files_inherits_its_section_lane():
    """No file info ⇒ the section's dominant lane, marked as inherited."""
    a = _entry("def-a", idents=["a_w"], vfile="theories/exp/bang.v")
    b = _entry("def-b", idents=["b_w"], vfile="theories/exp/seely.v")
    orphan = _entry("rem-x", idents=[])          # a remark with no source
    three = _three(paper=[_section("sec-x", [a, b, orphan])])

    byid = _byid(build_graph(three))
    assert byid["paper::rem-x"]["lane_id"] == "exponential"
    assert byid["paper::rem-x"]["band_id"] == "exp"
    assert byid["paper::rem-x"]["lane_src"] == "section"
    assert byid["paper::rem-x"]["layer_dir"] == ""
    # The group node carries the same dominant lane (the legacy section view
    # orders by it too).
    assert byid["grp::paper::sec-x"]["lane_id"] == "exponential"


def test_leaf_and_root_flags_on_a_known_sink(tmp_path):
    """``thm-master`` uses ``def-base`` ⇒ base is no leaf, master is no root.

    The flags are the point of the whole lane picture: a leaf is a headline
    result (nothing builds on it), a root is where a reading can start.  They
    are computed from the REAL dependency relation only — a prose mention of
    an entry must not stop it being a leaf.
    """
    demo = tmp_path / "theories" / "cbv"
    demo.mkdir(parents=True)
    (demo / "foo.v").write_text("(* source *)\n", encoding="utf-8")
    (demo / "foo.glob").write_text(_FIXTURE_GLOB, encoding="utf-8")

    base = _entry("def-base", idents=["base_lem"], vfile="theories/cbv/foo.v")
    master = _entry(
        "thm-master",
        idents=["master_thm"],
        snippet_html="the combinator and the master identity",
        vfile="theories/cbv/foo.v",
    )
    # A third entry nobody uses and which uses nobody: isolated, NOT a
    # headline result, so it is flagged apart from the real leaves.
    lonely = _entry("def-lonely", idents=["lonely_def"], vfile="theories/cbv/foo.v")
    three = _three(paper=[_section("sec-x", [base, master, lonely])])

    graph = build_graph(three, theories_root=tmp_path / "theories")
    byid = _byid(graph)

    assert byid["paper::def-base"]["leaf"] is False   # master depends on it
    assert byid["paper::def-base"]["root"] is True    # it depends on nothing
    assert byid["paper::thm-master"]["leaf"] is True  # nothing depends on it
    assert byid["paper::thm-master"]["root"] is False
    assert byid["paper::thm-master"]["isolated"] is False
    assert byid["paper::def-lonely"]["isolated"] is True

    meta = graph["meta"]
    assert meta["n_leaves"] == 2 and meta["n_isolated"] == 1
    # The flagged set excludes the isolated entry.
    assert meta["n_leaf_results"] == 1
    assert meta["leaves_by_tab"]["paper"] == 1


def test_prose_mentions_do_not_change_leaf_status():
    """A doc co-reference is not a dependency, and must not mark a leaf.

    With no ``.glob`` the graph still emits ``mentions`` edges; if those
    counted, an entry merely *named* in someone's prose would stop being a
    headline result and the flag would drift with the documentation's wording
    rather than with the proofs.
    """
    a = _entry("def-a", idents=["alpha_widget"], vfile="theories/homs/a.v")
    b = _entry(
        "def-b",
        idents=["beta_widget"],
        snippet_html=_name_span("alpha_widget"),
        vfile="theories/homs/b.v",
    )
    graph = build_graph(_three(paper=[_section("sec-x", [a, b])]))
    byid = _byid(graph)

    assert graph["meta"]["n_mentions"] > 0 and graph["meta"]["n_depends"] == 0
    assert byid["paper::def-a"]["leaf"] is True
    assert byid["paper::def-b"]["leaf"] is True
    # Nothing depends on anything ⇒ every entry is isolated, and the client
    # keys its marks off n_depends rather than flagging the whole canvas.
    assert graph["meta"]["n_leaf_results"] == 0


def test_meta_carries_the_lane_table_and_histogram():
    """The client sizes and captions lanes from ``meta``, not from literals."""
    three = _three(
        paper=[
            _section(
                "sec-x",
                [
                    _entry("def-a", idents=["a_w"], vfile="theories/cones/a.v"),
                    _entry("def-b", idents=["b_w"], vfile="theories/stable/b.v"),
                ],
            )
        ],
        ppl=[
            _section(
                "ppl-s",
                [_entry("ppl-a", idents=["p_w"], vfile="theories/programs/p.v")],
            )
        ],
    )
    meta = build_graph(three)["meta"]

    lanes = meta["lanes"]
    assert [lane["id"] for lane in lanes] == [
        "foundations",
        "measurable",
        "linear-stable",
        "exponential",
        "cbv",
        "ppl",
    ]
    assert [b["id"] for b in lanes[2]["bands"]] == ["homs", "stable"]
    assert lanes[2]["bands"][1]["dirs"] == ["stable"]
    # One row per tab, one column per lane, summing to that tab's entries.
    assert meta["lanes_by_tab"]["paper"] == [1, 0, 1, 0, 0, 0]
    assert meta["lanes_by_tab"]["ppl"] == [0, 0, 0, 0, 0, 1]
    assert meta["lanes_by_tab"]["examples"] == [0] * len(lanes)
    assert sum(meta["lanes_by_tab"]["paper"]) == meta["nodes_by_tab"]["paper"]["entries"]


def test_lane_fields_are_additive_and_always_present():
    """Every entry node carries the lane keys; old keys are untouched."""
    a = _entry("def-a", idents=["alpha"], vfile="theories/cbv/em.v")
    byid = _byid(build_graph(_three(paper=[_section("sec-x", [a])])))
    node = byid["paper::def-a"]

    for key in ("id", "label", "ntype", "tab", "parent", "url", "kind", "status"):
        assert key in node, key
    for key in (
        "lane", "lane_id", "band", "band_id", "layer_dir", "lane_src",
        "leaf", "root", "isolated",
    ):
        assert key in node, key


def _backward_graph(tmp_path, claim_files):
    """A graph with ONE dependency that runs against the lane order.

    ``thm-user`` is formalised in ``theories/prelude`` (lane 0) and its proof
    uses ``base_lem``; the entry that CLAIMS ``base_lem`` is placed by
    ``claim_files``.  Point those at a deeper layer and the resulting edge
    necessarily runs left → right against the lane reading.
    """
    src = tmp_path / "theories" / "prelude"
    src.mkdir(parents=True)
    (src / "x.v").write_text("(* source *)\n", encoding="utf-8")
    (src / "x.glob").write_text(_FIXTURE_GLOB, encoding="utf-8")

    claim = _entry("def-claim", idents=["base_lem"], vfile=claim_files)
    user = _entry("thm-user", idents=["master_thm"], vfile="theories/prelude/x.v")
    three = _three(paper=[_section("sec-x", [claim, user])])
    return build_graph(three, theories_root=tmp_path / "theories")


def test_backward_edges_are_flagged_on_the_edge(tmp_path):
    """A dependency against the lane order is MARKED, not merely counted.

    The hero used to promise that nothing on the left depends on anything to
    its right, and the canvas drew such edges exactly like the rest — so the
    reader who spotted one had already been told it could not exist.  The
    flag rides on the edge so the client can style the exception.
    """
    graph = _backward_graph(tmp_path, "theories/programs/ppl.v")
    byid = _byid(graph)
    assert byid["paper::thm-user"]["lane"] < byid["paper::def-claim"]["lane"]

    edge = next(
        e["data"]
        for e in graph["edges"]
        if e["data"]["source"] == "paper::thm-user"
        and e["data"]["target"] == "paper::def-claim"
    )
    assert edge["kind"] == "depends"
    assert edge["backward"] is True
    # Forward edges stay unflagged rather than carrying ``backward: False``:
    # the key means "this one is an exception".
    for e in graph["edges"]:
        if e["data"]["source"] != "paper::thm-user":
            assert "backward" not in e["data"]


def test_backward_edges_are_split_by_their_actual_cause(tmp_path):
    """Multi-layer placement and contested ident ownership are counted apart.

    Blaming every backward edge on "an entry documenting files from several
    layers is placed by its deepest one" is false whenever the target's files
    all live in ONE layer — there the placement rule cannot be at fault and
    the real cause is identifier ownership.  The two are counted separately
    so the page can say which is which.
    """
    contested = _backward_graph(tmp_path / "a", "theories/programs/ppl.v")
    assert contested["meta"]["n_lane_backward"] == 1
    assert contested["meta"]["n_lane_backward_contested"] == 1
    assert contested["meta"]["n_lane_backward_multilayer"] == 0

    spanning = _backward_graph(
        tmp_path / "b", ["theories/mcones/mcone.v", "theories/programs/ppl.v"]
    )
    assert spanning["meta"]["n_lane_backward"] == 1
    assert spanning["meta"]["n_lane_backward_multilayer"] == 1
    assert spanning["meta"]["n_lane_backward_contested"] == 0

    # The split is a partition of the total, in either build.
    for g in (contested, spanning):
        m = g["meta"]
        assert (
            m["n_lane_backward_multilayer"] + m["n_lane_backward_contested"]
            == m["n_lane_backward"]
        )


def test_lane_span_counts_lanes_not_files(tmp_path):
    """``lane_span`` is what tells the two causes apart, so pin its meaning.

    Two files in the SAME lane (even in the two parallel bands of it) are one
    lane, not two: a backward edge into such an entry is not explained by the
    max-layer placement rule.
    """
    one = _entry("def-one", idents=["a_w"], vfile="theories/exp/bang.v")
    parallel = _entry(
        "def-par",
        idents=["b_w"],
        vfile=["theories/homs/linhom.v", "theories/stable/scone.v"],
    )
    two = _entry(
        "def-two",
        idents=["c_w"],
        vfile=["theories/cones/precone.v", "theories/exp/bang.v"],
    )
    byid = _byid(
        build_graph(_three(paper=[_section("sec-x", [one, parallel, two])]))
    )
    assert byid["paper::def-one"]["lane_span"] == 1
    assert byid["paper::def-par"]["lane_span"] == 1   # one lane, two bands
    assert byid["paper::def-two"]["lane_span"] == 2


# -- real Coq dependency edges (.glob) --------------------------------------

# A minimal but format-faithful .glob: definition lines
# (``<kind> <bs>:<be> <modpath> <name>``) open a region; reference lines
# (``R<bs>:<be> <modpath> <dotpath> <localname> <refkind>``) belong to the
# region opened by the preceding definition line.  Here ``master_thm``'s
# region references ``base_lem`` (a real lemma use) and a notation (ignored).
_FIXTURE_GLOB = """DIGEST deadbeef
FIcones.demo.foo
R100:109 mathcomp.x <> measurable def
lem 200:210 <> base_lem
binder 211:211 <> U:1
R220:229 mathcomp.x <> ::scope:'='_x not
prf 300:318 <> master_thm
binder 319:319 <> U:2
R330:339 mathcomp.x <> measurable def
R350:357 Icones.demo.foo <> base_lem lem
R360:369 mathcomp.y <> ::scope:'+'_x not
"""


def test_parse_glob_uses_attributes_refs_to_owning_def():
    """A reference line belongs to the def-line region that precedes it."""
    uses = parse_glob_uses(_FIXTURE_GLOB)
    # master_thm's proof region references base_lem (a real lemma use); the
    # notation reference is filtered out (not a defined-object kind).
    assert "base_lem" in uses["master_thm"]
    # base_lem's own region references nothing of interest (only a notation).
    assert uses["base_lem"] == set()


def test_glob_depends_edge_between_entries(tmp_path):
    """A .glob-derived ``depends`` edge links a prover to its used lemma.

    Mirrors the motivating case: the entry documenting the combinator's
    master theorem has NO backticked mention of the base lemma in its prose,
    so only the .glob dependency surfaces the edge (it would be absent from
    the doc-co-reference relation).
    """
    # Lay out theories/demo/foo.{v,glob} so the loader finds the sibling glob.
    demo = tmp_path / "theories" / "demo"
    demo.mkdir(parents=True)
    (demo / "foo.v").write_text("(* source *)\n", encoding="utf-8")
    (demo / "foo.glob").write_text(_FIXTURE_GLOB, encoding="utf-8")

    base = _entry("def-base", idents=["base_lem"], vfile="theories/demo/foo.v")
    # The master entry's prose deliberately does NOT name base_lem.
    master = _entry(
        "thm-master",
        idents=["master_thm"],
        snippet_html="the combinator and the master identity",
        vfile="theories/demo/foo.v",
    )
    three = _three(examples=[_section("sec-x", [base, master])])

    edges, notices = build_glob_edges(three, tmp_path / "theories")
    assert (("examples", "thm-master"), ("examples", "def-base")) in edges
    assert notices == []  # glob present ⇒ no degradation notice

    # And the merged graph carries it as a ``depends`` edge (not ``mentions``).
    graph = build_graph(three, theories_root=tmp_path / "theories")
    kinds = {
        (e["data"]["source"], e["data"]["target"]): e["data"]["kind"]
        for e in graph["edges"]
    }
    assert kinds.get(("examples::thm-master", "examples::def-base")) == "depends"


def test_glob_missing_degrades_gracefully(tmp_path):
    """A missing .glob yields a NOTICE, no crash, and no depends edges."""
    demo = tmp_path / "theories" / "demo"
    demo.mkdir(parents=True)
    (demo / "foo.v").write_text("(* source, no sibling glob *)\n", encoding="utf-8")

    base = _entry("def-base", idents=["base_lem"], vfile="theories/demo/foo.v")
    master = _entry("thm-master", idents=["master_thm"], vfile="theories/demo/foo.v")
    three = _three(examples=[_section("sec-x", [base, master])])

    edges, notices = build_glob_edges(three, tmp_path / "theories")
    assert edges == []
    assert notices and any("glob" in n.lower() for n in notices)

    # build_graph still succeeds, falls back to mentions-only, and surfaces
    # the notice in meta — it must never crash or trip strict.
    graph = build_graph(three, theories_root=tmp_path / "theories")
    assert graph["meta"]["n_depends"] == 0
    assert graph["meta"]["notices"]
    # Every edge endpoint is still a real node (well-formed fallback).
    ids = {n["data"]["id"] for n in graph["nodes"]}
    for e in graph["edges"]:
        assert e["data"]["source"] in ids and e["data"]["target"] in ids


def test_graph_edges_carry_kind():
    """Every emitted edge carries a ``kind`` of ``depends`` or ``mentions``."""
    a = _entry("def-a", idents=["alpha_widget"], snippet_html="")
    b = _entry(
        "def-b", idents=["beta_widget"], snippet_html=_name_span("alpha_widget")
    )
    three = _three(paper=[_section("sec-x", [a, b])])

    graph = build_graph(three)  # theories_root=None ⇒ mentions only
    assert all(e["data"]["kind"] in {"depends", "mentions"} for e in graph["edges"])
    # With no theories root, all edges are mentions and a notice is recorded.
    assert all(e["data"]["kind"] == "mentions" for e in graph["edges"])
    assert graph["meta"]["notices"]


# -- the motivating real-repo case (guarded by .glob presence) --------------

def _repo_three():
    """Parse the live docs/PAPER|PPL|EXAMPLES into a ThreeTabDocument."""
    from tools.auditor.coqdoc import CoqdocResolver, parse_coqproject
    from tools.auditor.parser import parse_three_tabs

    repo = ROOT.parent  # ROOT == <repo>/tools ; the repo root is its parent
    cp = repo / "_CoqProject"
    if not cp.is_file():
        return None, None
    bindings = parse_coqproject(str(cp))
    resolver = CoqdocResolver(
        bindings=bindings, github_repo="x/y", commit="main", coqdoc_base="docs/"
    )
    three, _ = parse_three_tabs(
        paper_path=(repo / "docs" / "PAPER.md").resolve(),
        ppl_path=(repo / "docs" / "PPL.md").resolve(),
        examples_path=(repo / "docs" / "EXAMPLES.md").resolve(),
        resolver=resolver,
        project_root=repo,
        strict=False,
    )
    return three, repo


def test_real_glob_edges_add_dependencies_the_prose_misses():
    """The motivating property, stated without hard-coding entry ids.

    A proof routinely goes *through* a lemma the surrounding prose never
    backticks ("…by the master identity"), so the doc-co-reference relation
    cannot see it.  Parsing ``.glob`` is worth its complexity exactly to the
    extent that it recovers those: the real dependency relation must be both
    substantial and *not* a subset of the doc mentions.

    An earlier version of this test asserted one hard-coded id pair and
    silently rotted when ``docs/EXAMPLES.md`` was reorganised entry-per-
    concept; the property below survives renames while still failing loudly
    if the ``.glob`` pipeline stops producing real edges.

    Skips if docs/_CoqProject or the .glob files are absent (fresh checkout
    without -emit-glob).
    """
    import pytest

    three, repo = _repo_three()
    if three is None:
        pytest.skip("repo docs/_CoqProject not available")

    theories = repo / "theories"
    if not any(theories.rglob("*.glob")):
        pytest.skip(".glob files not built (fresh checkout / no -emit-glob)")

    dep, notices = build_glob_edges(three, theories)
    dep = set(dep)
    ment = set(build_entry_edges(three))

    assert len(dep) > 50, (
        f"only {len(dep)} real .glob dependency edges — the graph would be "
        "carried by doc co-references"
    )
    glob_only = dep - ment
    assert glob_only, (
        "every .glob dependency is also a doc mention — parsing .glob adds "
        "nothing, which contradicts its reason to exist"
    )
    # Every glob-only edge lands on real graph nodes (the relation is closed
    # over the node set the graph draws — sections, chapters AND Beyond).
    graph = build_graph(three, theories_root=theories)
    node_ids = {n["data"]["id"] for n in graph["nodes"]}
    for (s_tab, s_id), (t_tab, t_id) in glob_only:
        assert f"{s_tab}::{s_id}" in node_ids
        assert f"{t_tab}::{t_id}" in node_ids


# -- provenance + the strict guard ------------------------------------------


def test_glob_relation_reports_provenance(tmp_path):
    """``GlobRelation`` counts what was expected vs what was actually read."""
    from tools.auditor.glob_deps import build_glob_relation

    demo = tmp_path / "theories" / "demo"
    demo.mkdir(parents=True)
    (demo / "foo.v").write_text("(* source *)\n", encoding="utf-8")
    (demo / "foo.glob").write_text(_FIXTURE_GLOB, encoding="utf-8")
    (demo / "bar.v").write_text("(* no sibling glob *)\n", encoding="utf-8")

    base = _entry("def-base", idents=["base_lem"], vfile="theories/demo/foo.v")
    other = _entry("def-other", idents=["other_thm"], vfile="theories/demo/bar.v")
    three = _three(examples=[_section("sec-x", [base, other])])

    rel = build_glob_relation(three, tmp_path / "theories")
    assert rel.expected is True
    assert rel.available is True
    assert rel.n_vfiles == 2
    assert rel.n_glob_found == 1
    assert rel.n_glob_missing == 1
    assert rel.n_objects > 0
    assert "1/2" in rel.summary()

    # No theories root at all ⇒ nothing was expected, so the guard must not
    # treat the empty relation as a regression.
    none_rel = build_glob_relation(three, None)
    assert none_rel.expected is False
    assert none_rel.edges == [] and none_rel.notices


def test_strict_guard_trips_when_glob_data_is_missing(tmp_path):
    """Withholding the .glob files must FAIL the build, not degrade quietly."""
    import pytest

    from tools.auditor.render import GlobDependencyError, render

    demo = tmp_path / "theories" / "demo"
    demo.mkdir(parents=True)
    (demo / "foo.v").write_text("(* source, no sibling glob *)\n", encoding="utf-8")

    base = _entry("def-base", idents=["base_lem"], vfile="theories/demo/foo.v")
    master = _entry(
        "thm-master",
        idents=["master_thm"],
        snippet_html=_name_span("base_lem"),
        vfile="theories/demo/foo.v",
    )
    three = _three(paper=[_section("sec-x", [base, master])])

    with pytest.raises(GlobDependencyError):
        render(
            three,
            tmp_path / "site",
            theories_root=tmp_path / "theories",
            require_glob_deps=True,
        )

    # Same build, guard off ⇒ the degraded graph is still produced (the old
    # behaviour remains available for docs-only previews).
    totals = render(
        three,
        tmp_path / "site2",
        theories_root=tmp_path / "theories",
        require_glob_deps=False,
    )
    assert totals["graph_depends"] == 0
    assert totals["graph_mentions"] > 0


def test_strict_guard_passes_with_real_glob_data(tmp_path):
    """With .glob data present the same strict build succeeds."""
    from tools.auditor.render import render

    demo = tmp_path / "theories" / "demo"
    demo.mkdir(parents=True)
    (demo / "foo.v").write_text("(* source *)\n", encoding="utf-8")
    (demo / "foo.glob").write_text(_FIXTURE_GLOB, encoding="utf-8")

    base = _entry("def-base", idents=["base_lem"], vfile="theories/demo/foo.v")
    master = _entry("thm-master", idents=["master_thm"], vfile="theories/demo/foo.v")
    three = _three(paper=[_section("sec-x", [base, master])])

    totals = render(
        three,
        tmp_path / "site",
        theories_root=tmp_path / "theories",
        require_glob_deps=True,
    )
    assert totals["graph_depends"] >= 1
    graph = json.loads((tmp_path / "site" / "graph.json").read_text())
    assert graph["meta"]["glob_expected"] is True
    assert graph["meta"]["n_glob_files"] == 1


def test_guard_is_strict_in_ci_and_lenient_locally(monkeypatch):
    """Default strictness: on in CI, off on a dev box, env var always wins."""
    from tools.auditor.render import REQUIRE_GLOB_DEPS_ENV, require_glob_deps_default

    monkeypatch.delenv(REQUIRE_GLOB_DEPS_ENV, raising=False)
    monkeypatch.delenv("CI", raising=False)
    assert require_glob_deps_default() is False

    monkeypatch.setenv("CI", "true")
    assert require_glob_deps_default() is True

    monkeypatch.setenv(REQUIRE_GLOB_DEPS_ENV, "0")
    assert require_glob_deps_default() is False
    monkeypatch.delenv("CI", raising=False)
    monkeypatch.setenv(REQUIRE_GLOB_DEPS_ENV, "1")
    assert require_glob_deps_default() is True


# -- per-entry navigation from the same edge data ---------------------------


def test_attach_glob_relations_marks_and_adds_navigation_links(tmp_path):
    """Uses / Used-by cards carry the REAL dependency, marked ``via='glob'``."""
    from tools.auditor.xref import attach_entry_relations, attach_glob_relations

    demo = tmp_path / "theories" / "demo"
    demo.mkdir(parents=True)
    (demo / "foo.v").write_text("(* source *)\n", encoding="utf-8")
    (demo / "foo.glob").write_text(_FIXTURE_GLOB, encoding="utf-8")

    base = _entry("def-base", idents=["base_lem"], vfile="theories/demo/foo.v")
    # The master entry's prose does NOT name base_lem, so the doc pass alone
    # leaves it with no `uses` link at all.
    master = _entry(
        "thm-master",
        idents=["master_thm"],
        snippet_html="the combinator and the master identity",
        vfile="theories/demo/foo.v",
    )
    three = _three(paper=[_section("sec-x", [base, master])])

    attach_entry_relations(three)
    assert not [x for x in master.cross_refs if x.kind == "uses"]

    edges, _ = build_glob_edges(three, tmp_path / "theories")
    attach_glob_relations(three, edges)

    uses = [x for x in master.cross_refs if x.kind == "uses"]
    assert [(x.target, x.via) for x in uses] == [("def-base", "glob")]
    used_by = [x for x in base.cross_refs if x.kind == "used-by"]
    assert [(x.target, x.via) for x in used_by] == [("thm-master", "glob")]
    # Idempotent: a second pass must not duplicate the link.
    attach_glob_relations(three, edges)
    assert len([x for x in master.cross_refs if x.kind == "uses"]) == 1


def test_attach_glob_relations_upgrades_and_demotes(tmp_path):
    """A doc ref the .glob confirms is upgraded; one it does not is demoted."""
    from tools.auditor.schema import CrossRef
    from tools.auditor.xref import attach_glob_relations

    base = _entry("def-base", idents=["base_lem"], vfile="theories/demo/foo.v")
    master = _entry("thm-master", idents=["master_thm"], vfile="theories/demo/foo.v")
    zulu = _entry("def-zulu", idents=["zulu_lem"], vfile="theories/demo/foo.v")
    three = _three(paper=[_section("sec-x", [base, master, zulu])])

    # Two pre-existing doc co-references; only the `def-zulu` one is backed
    # by a real dependency below.
    master.cross_refs = [
        CrossRef(kind="uses", target="def-base", label="alpha", tab="paper", via="doc"),
        CrossRef(kind="uses", target="def-zulu", label="zulu", tab="paper", via="doc"),
    ]
    attach_glob_relations(
        three, [(("paper", "thm-master"), ("paper", "def-zulu"))]
    )

    # Only the proof-backed relation keeps the directional `uses` kind; the
    # unbacked one becomes an undirected co-reference (a dependency claim
    # the proofs do not support must not render as one).
    uses = [x for x in master.cross_refs if x.kind == "uses"]
    assert [(x.target, x.via) for x in uses] == [("def-zulu", "glob")]
    mentions = [x for x in master.cross_refs if x.kind == "mentions"]
    assert [(x.target, x.via) for x in mentions] == [("def-base", "doc")]
