"""The two relations a card may state, and the rules that keep them apart.

An auditor dashboard that says "Thm 4.19 · Used by · Thm 4.18" is making a
claim about the *proof*, and it had better be one.  Two independent defects
used to make that claim false, and both are pinned here:

1. **A prose mention is not a dependency.**  ``build_entry_edges`` derives
   ``A → B`` from *text overlap* — some token in ``A``'s statement / prose /
   snippet is an identifier ``B`` documents.  That relation is symmetric
   (pairs mention each other) and directionless: the sentence that minted
   the owner's bug is a *forward pointer* in Thm 4.18's prose telling the
   reader that the SAFT-engine lemmas are collected further down.  Such a
   pair is now filed as an undirected ``mentions`` co-reference on both
   entries, and ``uses`` / ``used-by`` are reserved for the ``.glob``
   relation — an invariant :func:`~tools.auditor.xref.attach_glob_relations`
   *enforces* rather than assumes.

2. **A shared object's internal step is not a dependency.**  Two entries may
   document the *same* Coq objects (Thm 4.19 and the ``SAFT engine`` entry
   document all three).  A reference running between objects they share says
   nothing about how the two entries relate, yet it published "Thm 4.19 is
   used by SAFT engine" — the glob-side half of the same bug on the same
   card.  Exactly that class is dropped, judged **per sourcing object**: a
   co-documented object's dependencies on *third* entries are real
   dependencies of every entry documenting it, and dropping those to spare
   this one would delete far more truth than it saves (§ 3).

Plus the provenance backfill, which recovers an entry's ``.v`` paths when
its Rocq cell spelled the sources as prose.  Note what that fixes and what
it does not: ``rocq_files`` is a *card-level* provenance claim and a
contribution to the build's **global** ``.glob`` scan set — it is not this
entry's private edge budget.  ``load_glob_uses`` merges ``{object: uses}``
across every scanned file, so an entry with no path of its own still sources
and receives edges as long as *some* entry names the file its objects live
in (§ 7).

And § 6 pins the canvas, because the same false claim can be *drawn* as
easily as written: an arrowhead on a co-reference edge says the identical
thing the panel was fixed to stop saying.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

#: The repository root — ``tools/auditor/tests/`` is three levels down.
REPO = Path(__file__).resolve().parents[3]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from tools.auditor.coqdoc import CoqdocResolver, parse_coqproject
from tools.auditor.glob_deps import build_claimant_map, build_glob_relation
from tools.auditor.parser import backfill_rocq_files, parse_three_tabs
from tools.auditor.schema import (
    CoqSnippet,
    CrossRef,
    Document,
    Entry,
    EntryDetail,
    RocqFile,
    Section,
    ThreeTabDocument,
)
from tools.auditor.snippets import SnippetResolver
from tools.auditor.xref import (
    MENTION_KIND,
    attach_entry_relations,
    attach_glob_relations,
)

#: Directional relation kinds — the ones that make a dependency claim.
DIRECTIONAL = ("uses", "used-by")


# -- fixtures ---------------------------------------------------------------


def _name_span(ident: str) -> str:
    return f'<span class="n">{ident}</span>'


def _entry(eid: str, idents=(), snippet_html: str = "", vfile="", prose="") -> Entry:
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
            prose_html=prose,
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


#: Two entries documenting the SAME pair of objects, mirroring the real
#: ``Thm 4.19`` / ``SAFT engine`` overlap.  ``wi_med``'s region makes two
#: references, and the whole point of the policy is that they are treated
#: differently:
#:   * to ``wi_obj`` — the other object of the SHARED pair: an internal step
#:     of one object set, which says nothing about how the two entries
#:     documenting it relate;
#:   * to ``outer_lemma`` — a THIRD entry's object: a real dependency, and a
#:     real dependency of *both* entries that document ``wi_med``.
#: ``tensor_thing`` (a third entry's object) also references ``wi_obj``, a
#: genuine cross-entry dependency onto a co-documented object.
_CO_OWNED_GLOB = """DIGEST deadbeef
FIcones.demo.foo
def 100:110 <> wi_obj
lem 200:215 <> wi_med
R220:229 Icones.demo.foo <> wi_obj def
R240:249 Icones.demo.foo <> outer_lemma def
prf 300:318 <> tensor_thing
R330:339 Icones.demo.foo <> wi_obj def
def 400:412 <> outer_lemma
"""


def _co_owned_tree(tmp_path: Path) -> Path:
    demo = tmp_path / "theories" / "demo"
    demo.mkdir(parents=True)
    (demo / "foo.v").write_text("(* source *)\n", encoding="utf-8")
    (demo / "foo.glob").write_text(_CO_OWNED_GLOB, encoding="utf-8")
    return tmp_path / "theories"


def _co_owned_doc() -> ThreeTabDocument:
    vfile = "theories/demo/foo.v"
    thm = _entry("thm-4-19", idents=["wi_obj", "wi_med"], vfile=vfile)
    saft = _entry("saft-engine", idents=["wi_obj", "wi_med"], vfile=vfile)
    tensor = _entry("tensor-as-saft", idents=["tensor_thing"], vfile=vfile)
    outer = _entry("outer-page", idents=["outer_lemma"], vfile=vfile)
    return _three(paper=[_section("sec-x", [thm, saft, tensor, outer])])


@pytest.fixture(scope="module")
def corpus():
    """The real dashboard, parsed from ``docs/`` with the real ``.glob``s.

    The owner's bug was in the shipped data, not in a fixture, so the
    regressions that matter are asserted against the shipped data.
    """
    docs = REPO / "docs"
    theories = REPO / "theories"
    if not (docs / "PAPER.md").is_file():
        pytest.skip("docs/PAPER.md not available")
    if not any(theories.rglob("*.glob")):
        pytest.skip("no .glob files — build theories/ first")
    resolver = CoqdocResolver(
        bindings=parse_coqproject(str(REPO / "_CoqProject")),
        github_repo="icones/icones-rocq",
        commit="HEAD",
        coqdoc_base="",
    )
    three, _warns = parse_three_tabs(
        paper_path=docs / "PAPER.md",
        ppl_path=docs / "PPL.md",
        examples_path=docs / "EXAMPLES.md",
        resolver=resolver,
        project_root=REPO,
    )
    attach_entry_relations(three)
    rel = build_glob_relation(three, theories)
    attach_glob_relations(three, rel.edges)
    return three, rel


def _entries(three: ThreeTabDocument):
    """``(tab, entry)`` for every distinct entry of the document."""
    seen: set[int] = set()
    for tab in ("paper", "ppl", "examples"):
        doc = three.tab(tab)
        groups = list(doc.sections)
        groups += [s for c in doc.chapters for s in c.sections]
        groups += list(doc.beyond)
        for group in groups:
            for entry in group.entries:
                if id(entry) in seen:
                    continue
                seen.add(id(entry))
                yield tab, entry


def _find(three: ThreeTabDocument, tab: str, eid: str) -> Entry:
    for t, entry in _entries(three):
        if t == tab and entry.id == eid:
            return entry
    raise AssertionError(f"entry {tab}/{eid} not found")


# -- 1. no doc-derived edge may occupy a dependency slot ---------------------


def test_no_doc_ref_renders_in_a_dependency_slot(corpus):
    """THE invariant: every Uses / Used-by link is proof-backed.

    ``uses`` / ``used-by`` are the only refs the card renders under a
    directional verb, so a ``via='doc'`` ref in one of those slots is a
    published falsehood.  Asserted over the whole shipped corpus.
    """
    three, _rel = corpus
    offenders = [
        (tab, entry.id, ref.kind, ref.target, ref.via)
        for tab, entry in _entries(three)
        for ref in entry.cross_refs
        if ref.kind in DIRECTIONAL and ref.via != "glob"
    ]
    assert offenders == [], (
        f"{len(offenders)} directional relation(s) are not backed by the "
        f".glob data, e.g. {offenders[:5]}"
    )


def test_doc_co_references_are_undirected_and_labelled(corpus):
    """Doc co-references exist, carry ``via='doc'`` and are symmetric.

    The relation is only honest if BOTH entries state it the same way: a
    ``mentions`` ref on A with no matching ref on B would be a direction
    wearing a different name.
    """
    three, _rel = corpus
    pairs: set[tuple[tuple[str, str], tuple[str, str]]] = set()
    n = 0
    for tab, entry in _entries(three):
        for ref in entry.cross_refs:
            if ref.kind != MENTION_KIND:
                continue
            n += 1
            assert ref.via == "doc", f"{entry.id} -> {ref.target} via {ref.via!r}"
            pairs.add(((tab, entry.id), (ref.tab, ref.target)))
    assert n, "no doc co-references at all — the relation vanished"
    asymmetric = [(a, b) for a, b in pairs if (b, a) not in pairs]
    assert asymmetric == [], (
        f"{len(asymmetric)} co-reference(s) are stated on one side only, "
        f"e.g. {asymmetric[:5]}"
    )


def test_mentions_never_duplicate_a_proof_relation(corpus):
    """A partner already stated as a dependency is not re-stated weakly."""
    three, _rel = corpus
    for _tab, entry in _entries(three):
        proof = {
            (r.tab, r.target) for r in entry.cross_refs if r.kind in DIRECTIONAL
        }
        dupes = [
            r.target
            for r in entry.cross_refs
            if r.kind == MENTION_KIND and (r.tab, r.target) in proof
        ]
        assert dupes == [], f"{entry.id} states {dupes} both ways"


# -- 2. the owner's exemplar ------------------------------------------------


def test_thm_4_18_and_thm_4_19_have_no_directional_doc_edge(corpus):
    """The reported bug, pinned on the real entries.

    Thm 4.18's prose points the reader *forward* to the SAFT-engine
    lemmas ("… is collected under *Beyond the paper* below").  Nothing in
    that sentence is a dependency, in either direction: the pair may only
    appear as an undirected co-reference.
    """
    three, rel = corpus
    thm18 = _find(three, "paper", "thm-4-18")
    thm19 = _find(three, "paper", "thm-4-19")

    for entry, partner in ((thm18, "thm-4-19"), (thm19, "thm-4-18")):
        directional = [
            (r.kind, r.via)
            for r in entry.cross_refs
            if r.kind in DIRECTIONAL and r.target == partner
        ]
        assert directional == [], (
            f"{entry.id} still claims a dependency on {partner}: {directional}"
        )
        co_ref = [r for r in entry.cross_refs if r.target == partner]
        assert [r.kind for r in co_ref] == [MENTION_KIND], (
            f"{entry.id} -> {partner} should be a lone co-reference, "
            f"got {[(r.kind, r.via) for r in co_ref]}"
        )

    # …and the proofs really do not relate them, in either direction.
    pair = {(("paper", "thm-4-18"), ("paper", "thm-4-19")),
            (("paper", "thm-4-19"), ("paper", "thm-4-18"))}
    assert not (pair & set(rel.edges))


def test_thm_4_19_keeps_only_its_real_dependents(corpus):
    """Its Used-by list is the genuine one, not the co-ownership artifact.

    ``SAFT engine`` documents the same three objects as Thm 4.19, so
    ``wi_med``'s reference to ``wi_obj`` — an internal fact about one file
    — used to surface as "Thm 4.19 is used by SAFT engine".
    """
    three, _rel = corpus
    thm19 = _find(three, "paper", "thm-4-19")
    used_by = {r.target for r in thm19.cross_refs if r.kind == "used-by"}
    assert "saft-engine" not in used_by
    assert "tensor-as-saft-left-adjoint" in used_by, (
        "the genuine dependent was lost with the bogus one"
    )


def test_thm_4_19_has_its_source_files(corpus):
    """Provenance: the card names the file its identifiers actually live in.

    This is a *display* claim — "here is where this entry's Rocq lives" —
    and the second thing the owner reported.  It is emphatically NOT the
    reason Thm 4.19 has proof-level edges: the scan set is global (see
    :func:`test_edges_do_not_depend_on_one_entrys_own_paths`).
    """
    three, _rel = corpus
    thm19 = _find(three, "paper", "thm-4-19")
    paths = [rf.path for rf in thm19.rocq_files]
    assert "theories/homs/representable.v" in paths, paths


def test_every_ident_bearing_entry_has_source_files(corpus):
    """No entry documents identifiers from nowhere."""
    three, _rel = corpus
    orphans = [
        f"{tab}/{entry.id}"
        for tab, entry in _entries(three)
        if entry.rocq_idents and not entry.rocq_files
    ]
    assert orphans == [], f"entries with idents but no .v files: {orphans}"


# -- 3. co-documentation policy ---------------------------------------------


def test_claimant_map_lists_every_documenting_entry():
    """No arbitration: a co-documented ident keeps ALL of its claimants.

    Picking one "owner" and silencing the rest is what cost the corpus 44
    true edges — a second entry documenting an object documents it, and its
    dependencies are that entry's dependencies too.
    """
    three = _co_owned_doc()
    owners = [("paper", e.id, e) for e in three.paper.sections[0].entries]
    claimants = build_claimant_map(owners)

    assert claimants["wi_obj"] == [("paper", "thm-4-19"), ("paper", "saft-engine")]
    assert claimants["wi_med"] == [("paper", "thm-4-19"), ("paper", "saft-engine")]
    assert claimants["tensor_thing"] == [("paper", "tensor-as-saft")]


def test_co_documented_objects_do_not_depend_on_each_other(tmp_path):
    """The glob-side half of the owner's bug, on a fixture.

    A reference between two objects that BOTH entries document is internal
    to the shared set and states nothing about the pair — while a genuine
    dependency onto one of those same objects, from outside, survives.
    """
    theories = _co_owned_tree(tmp_path)
    rel = build_glob_relation(_co_owned_doc(), theories)

    bogus = (("paper", "saft-engine"), ("paper", "thm-4-19"))
    inbound = (("paper", "tensor-as-saft"), ("paper", "thm-4-19"))
    assert bogus not in rel.edges
    assert inbound in rel.edges
    assert bogus in rel.suppressed
    assert set(rel.contested) == {"wi_obj", "wi_med"}


def test_a_shared_objects_third_party_deps_survive_for_every_claimant(tmp_path):
    """THE regression that a one-owner policy caused: 44 true edges deleted.

    ``wi_med`` uses ``outer_lemma``, which a THIRD entry documents.  That is
    a real dependency, and it belongs to *both* entries documenting
    ``wi_med`` — silencing the non-"owner" is what dropped
    ``ex-bayes-linear`` from 17 proof-backed relations to 4 and deleted
    ``-> def-4-2`` from the graph outright.
    """
    theories = _co_owned_tree(tmp_path)
    rel = build_glob_relation(_co_owned_doc(), theories)

    for claimant in ("thm-4-19", "saft-engine"):
        edge = (("paper", claimant), ("paper", "outer-page"))
        assert edge in rel.edges, f"{claimant} lost a real dependency"
        assert edge not in rel.suppressed


def test_only_the_internal_class_is_ever_suppressed(tmp_path):
    """The exclusion is exactly "target co-documents the sourcing object".

    Stated as an invariant over the whole fixture rather than by example,
    so a future widening of the rule fails here instead of quietly costing
    real edges again.
    """
    theories = _co_owned_tree(tmp_path)
    three = _co_owned_doc()
    rel = build_glob_relation(three, theories)
    claimants = build_claimant_map(
        [("paper", e.id, e) for e in three.paper.sections[0].entries]
    )

    for src, tgt in rel.suppressed:
        shared = [i for i, who in claimants.items() if src in who and tgt in who]
        assert shared, f"{src} -> {tgt} suppressed but shares no object"


def test_the_policys_decisions_are_listed_in_the_build_report(tmp_path):
    """Every edge the policy drops, and every shared name, is in the log."""
    theories = _co_owned_tree(tmp_path)
    rel = build_glob_relation(_co_owned_doc(), theories)
    report = "\n".join(rel.report_lines())

    assert "co-documentation policy" in report
    assert "`wi_obj` -> paper/thm-4-19, paper/saft-engine" in report
    assert "paper/saft-engine -> paper/thm-4-19" in report
    # …and it does not claim to have taken anything else away.
    assert "paper/saft-engine -> paper/outer-page" not in report


def test_policy_is_subtractive_never_reversing(tmp_path):
    """The policy may only remove edges — never invent or flip one."""
    theories = _co_owned_tree(tmp_path)
    rel = build_glob_relation(_co_owned_doc(), theories)
    kept, dropped = set(rel.edges), set(rel.suppressed)
    assert not (kept & dropped)
    assert all((tgt, src) not in kept for src, tgt in dropped)


def test_short_names_may_still_source_dependencies(tmp_path):
    """A 2-char Coq object is unambiguous in ``.glob`` and stays eligible.

    The text matcher drops names under four characters (they over-link in
    prose); a ``.glob`` object name needs no such guard, and applying one
    would silently delete real dependencies.
    """
    demo = tmp_path / "theories" / "demo"
    demo.mkdir(parents=True)
    (demo / "foo.v").write_text("(* source *)\n", encoding="utf-8")
    (demo / "foo.glob").write_text(
        "DIGEST deadbeef\n"
        "FIcones.demo.foo\n"
        "def 100:110 <> base_lemma\n"
        "lem 200:215 <> eD\n"
        "R220:229 Icones.demo.foo <> base_lemma def\n",
        encoding="utf-8",
    )
    base = _entry("def-base", idents=["base_lemma"], vfile="theories/demo/foo.v")
    short = _entry("term-interp", idents=["eD"], vfile="theories/demo/foo.v")
    three = _three(paper=[_section("sec-x", [base, short])])

    rel = build_glob_relation(three, tmp_path / "theories")
    assert (("paper", "term-interp"), ("paper", "def-base")) in rel.edges


# -- 4. the demotion invariant, on fixtures ---------------------------------


def test_doc_relation_is_filed_undirected_on_both_entries():
    """Text overlap yields one co-reference, stated identically both ways."""
    owner = _entry("def-widget", idents=["shared_widget"])
    mentioner = _entry(
        "thm-user", idents=["user_thm"], snippet_html=_name_span("shared_widget")
    )
    three = _three(paper=[_section("sec-x", [owner, mentioner])])
    attach_entry_relations(three)

    for entry, partner in ((owner, "thm-user"), (mentioner, "def-widget")):
        kinds = [(r.kind, r.via) for r in entry.cross_refs if r.target == partner]
        assert kinds == [(MENTION_KIND, "doc")], f"{entry.id}: {kinds}"
        assert not [r for r in entry.cross_refs if r.kind in DIRECTIONAL]


def test_attach_glob_relations_demotes_unbacked_directional_refs():
    """A legacy / hand-written directional doc ref cannot survive.

    The invariant is enforced, not trusted: whatever the input payload
    claims, an unconfirmed direction comes out as a co-reference.
    """
    base = _entry("def-base", idents=["base_lem"])
    master = _entry("thm-master", idents=["master_thm"])
    three = _three(paper=[_section("sec-x", [base, master])])
    master.cross_refs = [
        CrossRef(kind="uses", target="def-base", label="base", tab="paper", via="doc"),
        CrossRef(
            kind="used-by", target="def-base", label="base", tab="paper", via="doc"
        ),
    ]

    attach_glob_relations(three, [])  # no proof-level data at all

    assert not [r for r in master.cross_refs if r.kind in DIRECTIONAL]
    assert [(r.kind, r.target, r.via) for r in master.cross_refs] == [
        (MENTION_KIND, "def-base", "doc")
    ]


def test_attach_glob_relations_is_idempotent():
    """Re-running the pass neither duplicates nor re-demotes."""
    base = _entry("def-base", idents=["base_lem"])
    master = _entry("thm-master", idents=["master_thm"])
    three = _three(paper=[_section("sec-x", [base, master])])
    edges = [(("paper", "thm-master"), ("paper", "def-base"))]

    attach_glob_relations(three, edges)
    first = [(r.kind, r.target, r.via) for r in master.cross_refs]
    attach_glob_relations(three, edges)
    assert [(r.kind, r.target, r.via) for r in master.cross_refs] == first
    assert first == [("uses", "def-base", "glob")]


# -- 5. the panel itself ----------------------------------------------------


def _render_panel(entry: Entry) -> str:
    """Render just the relations panel for ``entry``."""
    from tools.auditor.render import _make_env

    env = _make_env(None)
    env.globals.update(
        xref_href=lambda x: f"../entries/{x.target}.html",
        tab_prefix="../../",
        tab="paper",
    )
    tmpl = env.from_string(
        "{% import '_macros.html' as m %}{{ m.xref_panel(entry) }}"
    )
    return tmpl.render(entry=entry)


def _row(html: str, cls: str) -> str:
    """The rendered text of one panel row (``''`` when absent)."""
    import re

    m = re.search(
        rf'<p class="xrefs xref-{cls}">(.*?)</p>', html, re.S
    )
    return re.sub(r"\s+", " ", m.group(1)) if m else ""


def test_panel_rows_keep_the_two_relations_apart():
    """A co-reference renders under its own direction-free heading.

    The panel is where the false claim was actually published, so the row
    assignment is pinned here: nothing doc-derived may appear under "Uses"
    or "Used by", and the co-reference row must not borrow a verb.
    """
    entry = _entry("thm-4-19", idents=["wi_obj"])
    entry.cross_refs = [
        CrossRef(kind="uses", target="cat-4", label="Cat 4", tab="paper", via="glob"),
        CrossRef(
            kind="used-by",
            target="tensor-as-saft-left-adjoint",
            label="Tensor as SAFT left adjoint",
            tab="paper",
            via="glob",
        ),
        CrossRef(
            kind=MENTION_KIND,
            target="thm-4-18",
            label="Thm 4.18",
            tab="paper",
            via="doc",
        ),
    ]
    html = _render_panel(entry)

    assert "Thm 4.18" not in _row(html, "uses")
    assert "Thm 4.18" not in _row(html, "used-by")
    mentions_row = _row(html, "mentions")
    assert "Thm 4.18" in mentions_row
    assert "Mentioned with:" in html
    # No directional verb anywhere near the co-reference row.
    assert "Used by" not in mentions_row and "Uses" not in mentions_row
    # Counts are reported per relation, never summed into one number.
    assert "Uses <b>1</b>" in html and "Used by <b>1</b>" in html
    assert "Mentioned with <b>1</b>" in html


def test_panel_explains_itself_when_nothing_is_proof_backed():
    """A co-reference-only panel still carries the caveat.

    The legend used to be gated on there being proof-backed links, so the
    panels made ENTIRELY of prose inference were the only ones that
    explained nothing.
    """
    entry = _entry("def-2-1", idents=["precone_thing"])
    entry.cross_refs = [
        CrossRef(
            kind=MENTION_KIND,
            target="def-2-2",
            label="Def 2.2",
            tab="paper",
            via="doc",
        )
    ]
    import re

    html = _render_panel(entry)
    flat = re.sub(r"\s+", " ", html)

    assert "xref-legend" in html
    assert "not a dependency" in flat
    assert "points in no direction" in flat
    assert '<p class="xrefs xref-uses">' not in html
    assert '<p class="xrefs xref-used-by">' not in html


# -- 6. the graph canvas ----------------------------------------------------


def test_graph_canvas_draws_no_arrowhead_on_a_co_reference():
    """The same falsehood, one click away, drawn instead of written.

    ``graph.js`` puts ``source-arrow-shape: "triangle"`` on the BASE ``edge``
    selector, so every edge is arrowed unless its own rule turns that off.
    A ``mentions`` edge with an arrowhead is a direction claim on a relation
    that has none — the panel's "See this entry in the graph →" link led
    straight to it.  Pinned as source text because there is no JS runner
    here, and the whole defect was one missing override.
    """
    js = (REPO / "tools" / "auditor" / "static" / "graph.js").read_text(
        encoding="utf-8"
    )
    start = js.index('selector: "edge.mentions"')
    rule = js[start : js.index("},", js.index("style:", start))]
    for prop in ("source-arrow-shape", "target-arrow-shape"):
        assert f'"{prop}": "none"' in rule, (
            f"edge.mentions does not clear {prop}; the base `edge` rule's "
            "arrowhead then draws a direction on an undirected relation"
        )


# -- 7. provenance backfill -------------------------------------------------


def _resolver_for(tmp_path: Path) -> tuple[SnippetResolver, CoqdocResolver]:
    return (
        SnippetResolver(tmp_path / "theories", repo_root=tmp_path),
        CoqdocResolver(
            bindings=parse_coqproject(str(REPO / "_CoqProject")),
            github_repo="icones/icones-rocq",
            commit="HEAD",
            coqdoc_base="",
        ),
    )


def _write_theories(tmp_path: Path, files: dict[str, str]) -> None:
    for rel, body in files.items():
        path = tmp_path / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")


def test_backfill_recovers_files_from_the_ident_index(tmp_path):
    """A doc that names identifiers but no path still gets its sources."""
    _write_theories(
        tmp_path,
        {
            "theories/homs/representable.v": (
                "Definition wi_obj (x : nat) : nat := x.\n"
                "Lemma wi_med : True. Proof. exact I. Qed.\n"
            )
        },
    )
    snips, coqdoc = _resolver_for(tmp_path)
    entry = _entry("thm-4-19", idents=["wi_obj", "wi_med"])
    assert entry.rocq_files == []

    notices = backfill_rocq_files([entry], snips, coqdoc, tab="paper")

    assert [rf.path for rf in entry.rocq_files] == [
        "theories/homs/representable.v"
    ]
    assert len(notices) == 1
    # The report names the entry, the recovered file and the idents that
    # led there — a silent backfill would be its own provenance problem.
    assert "thm-4-19" in notices[0]
    assert "theories/homs/representable.v" in notices[0]
    assert "wi_obj" in notices[0]


def test_backfill_leaves_documented_files_alone(tmp_path):
    """It fires only where the docs gave nothing.

    Unioning index hits into a non-empty list would hand an entry the file
    of every identifier it merely mentions in passing.
    """
    _write_theories(
        tmp_path,
        {
            "theories/a.v": "Definition alpha_thing := 0.\n",
            "theories/b.v": "Definition beta_thing := 1.\n",
        },
    )
    snips, coqdoc = _resolver_for(tmp_path)
    entry = _entry(
        "some-entry", idents=["alpha_thing", "beta_thing"], vfile="theories/a.v"
    )

    notices = backfill_rocq_files([entry], snips, coqdoc)

    assert [rf.path for rf in entry.rocq_files] == ["theories/a.v"]
    assert notices == []


def test_edges_do_not_depend_on_one_entrys_own_paths(tmp_path):
    """The scan set is GLOBAL: a path-less entry still gets its edges.

    Pinning the real model, because the tempting one is wrong and was
    briefly written down as fact.  ``rocq_files`` is a card-level
    provenance claim plus a contribution to a union scan set; it is not the
    entry's private edge budget.  ``base`` here names no ``.v`` file at all,
    and still both sources and receives proof-level edges, because ``user``
    put the shared file in the scan set.
    """
    demo = tmp_path / "theories" / "demo"
    demo.mkdir(parents=True)
    (demo / "foo.v").write_text("(* source *)\n", encoding="utf-8")
    (demo / "foo.glob").write_text(
        "DIGEST deadbeef\n"
        "FIcones.demo.foo\n"
        "def 100:110 <> deep_lemma\n"
        "lem 200:215 <> base_lemma\n"
        "R220:229 Icones.demo.foo <> deep_lemma def\n"
        "thm 300:318 <> user_thm\n"
        "R330:339 Icones.demo.foo <> base_lemma def\n",
        encoding="utf-8",
    )
    deep = _entry("def-deep", idents=["deep_lemma"], vfile="theories/demo/foo.v")
    base = _entry("def-base", idents=["base_lemma"])          # NO path
    user = _entry("thm-user", idents=["user_thm"], vfile="theories/demo/foo.v")
    three = _three(paper=[_section("sec-x", [deep, base, user])])
    assert base.rocq_files == []

    rel = build_glob_relation(three, tmp_path / "theories")

    assert (("paper", "def-base"), ("paper", "def-deep")) in rel.edges
    assert (("paper", "thm-user"), ("paper", "def-base")) in rel.edges


def test_backfill_refuses_ambiguous_and_unknown_idents(tmp_path):
    """A name declared in two files (or in none) contributes nothing."""
    _write_theories(
        tmp_path,
        {
            "theories/one.v": "Definition twin_thing := 0.\n",
            "theories/two.v": "Definition twin_thing := 1.\n",
        },
    )
    snips, coqdoc = _resolver_for(tmp_path)
    ambiguous = _entry("amb", idents=["twin_thing"])
    unknown = _entry("unk", idents=["no_such_ident"])

    notices = backfill_rocq_files([ambiguous, unknown], snips, coqdoc)

    assert ambiguous.rocq_files == []
    assert unknown.rocq_files == []
    assert notices == []
