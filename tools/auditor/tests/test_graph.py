"""Tests for the dependency-graph data emission (``tools.auditor.graph``).

The graph reuses the xref relation (entry A references an identifier owned
by entry B ⇒ edge A→B) and the parsed Document hierarchy (tab → group →
entry compound nesting).  These tests check the emitted data is well
formed: every edge endpoint is a real node, no self-edges, parents resolve,
entry URLs follow the page route, and the hierarchy is carried.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT.parent) not in sys.path:
    sys.path.insert(0, str(ROOT.parent))

from tools.auditor.graph import build_graph
from tools.auditor.schema import (
    CoqSnippet,
    Document,
    Entry,
    EntryDetail,
    Section,
    ThreeTabDocument,
)
from tools.auditor.xref import build_entry_edges


def _name_span(ident: str) -> str:
    return f'<span class="n">{ident}</span>'


def _entry(eid: str, idents, snippet_html: str = "") -> Entry:
    return Entry(
        id=eid,
        paper_label=eid,
        paper_kind="Def",
        paper_number=None,
        paper_section_id="sec-x",
        statement_html="",
        rocq_idents=list(idents),
        rocq_files=[],
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
    """A PPL entry referencing a Paper-owned ident yields a cross-tab edge."""
    paper = _entry("thm-9-7", idents=["EM_term"], snippet_html="")
    ppl = _entry(
        "ppl-x", idents=["tyD_cbv"], snippet_html=_name_span("EM_term")
    )
    three = _three(paper=[_section("sec-x", [paper])], ppl=[_section("ppl-s", [ppl])])

    graph = build_graph(three)
    edge_pairs = {
        (e["data"]["source"], e["data"]["target"]) for e in graph["edges"]
    }
    assert ("ppl::ppl-x", "paper::thm-9-7") in edge_pairs


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
