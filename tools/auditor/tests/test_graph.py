"""Tests for the dependency-graph data emission (``tools.auditor.graph``).

The graph reuses the xref relation (entry A references an identifier owned
by entry B ⇒ edge A→B) and the parsed Document hierarchy (tab → group →
entry compound nesting).  These tests check the emitted data is well
formed: every edge endpoint is a real node, no self-edges, parents resolve,
entry URLs follow the page route, and the hierarchy is carried.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT.parent) not in sys.path:
    sys.path.insert(0, str(ROOT.parent))

from tools.auditor.glob_deps import build_glob_edges, parse_glob_uses
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


def _entry(eid: str, idents, snippet_html: str = "", vfile: str = "") -> Entry:
    return Entry(
        id=eid,
        paper_label=eid,
        paper_kind="Def",
        paper_number=None,
        paper_section_id="sec-x",
        statement_html="",
        rocq_idents=list(idents),
        rocq_files=(
            [
                RocqFile(
                    path=vfile,
                    section=None,
                    github_url="",
                    coqdoc_url=None,
                    coqdoc_anchor=None,
                )
            ]
            if vfile
            else []
        ),
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


def test_attach_glob_relations_upgrades_and_orders(tmp_path):
    """A doc ref the .glob confirms is upgraded; proof-backed links sort first."""
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

    uses = [x for x in master.cross_refs if x.kind == "uses"]
    assert [x.target for x in uses] == ["def-zulu", "def-base"]  # glob first
    assert [x.via for x in uses] == ["glob", "doc"]
