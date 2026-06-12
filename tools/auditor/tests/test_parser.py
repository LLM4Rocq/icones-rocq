"""Parser tests using small golden Markdown fixtures.

Each fixture lives in ``golden/NN_*.md`` and exercises a single document
shape.  The assertions check that the parser produces the structural
output the UI agent will consume.
"""

from __future__ import annotations

from pathlib import Path

import pytest

# Make ``tools.auditor`` importable when running from the repo root.
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT.parent) not in sys.path:
    sys.path.insert(0, str(ROOT.parent))

from tools.auditor.classifier import classify, DEFAULT_REGRESSION_ANCHORS
from tools.auditor.coqdoc import CoqProjectBinding, CoqdocResolver, parse_coqproject
from tools.auditor.parser import (
    parse,
    parse_tabs,
    parse_three_tabs,
    parse_two_tabs,
    slugify_label,
    _classify_paper_label_kind,  # noqa: PLC2701 — tested intentionally
    _split_table_row,  # noqa: PLC2701
)
from tools.auditor.schema import (
    ALL_TABS,
    TAB_EXAMPLES,
    TAB_PAPER,
    TAB_PPL,
    ThreeTabDocument,
    TwoTabDocument,
    three_tab_to_dict,
    two_tab_to_dict,
)


GOLDEN = Path(__file__).parent / "golden"


def _resolver(repo: str = "demo/demo", commit: str = "abc123") -> CoqdocResolver:
    bindings = [CoqProjectBinding(physical="theories", logical="Icones")]
    return CoqdocResolver(bindings=bindings, github_repo=repo, commit=commit)


# -- pure-function tests ----------------------------------------------------


def test_slugify_paper_labels():
    assert slugify_label("Def 2.1") == "def-2-1"
    assert slugify_label("Lem 2.8 / 2.10") == "lem-2-8-2-10"
    assert slugify_label("Lem 7.20–7.25") == "lem-7-20-7-25"
    assert slugify_label("§ 8") == "sec-8"
    # § -> "sec-"; the parens-wrapped section reference becomes "sec-4".
    assert slugify_label("Fubini (§4)") == "fubini-sec-4"
    assert slugify_label("Cat 2") == "cat-2"
    assert slugify_label("ARCAT") == "arcat"
    assert slugify_label("§9.2") == "sec-9-2"
    # Truncation safety
    assert len(slugify_label("a " * 200)) <= 80


def test_classify_paper_label_kind():
    assert _classify_paper_label_kind("Def 2.1") == ("Def", "2.1")
    assert _classify_paper_label_kind("Lem 2.8 / 2.10") == ("Lem", "2.8 / 2.10")
    assert _classify_paper_label_kind("Cat 2") == ("Cat", "2")
    assert _classify_paper_label_kind("Thm 6.5") == ("Thm", "6.5")
    assert _classify_paper_label_kind("Fubini (§4)") == ("Fubini", None)
    assert _classify_paper_label_kind("Prop 5.8") == ("Prop", "5.8")
    # "§ 8" is currently treated as kind=Other; the trailing number is
    # not captured because the leading § does not have its own kind group.
    kind, _ = _classify_paper_label_kind("§ 8")
    assert kind == "Other"
    assert _classify_paper_label_kind("ARCAT") == ("Other", None)
    assert _classify_paper_label_kind("(also)") == ("Other", None)


def test_split_table_row_handles_backticks():
    cells = _split_table_row("| Def 2.1 | A *precone* is a thing. | `a`, `b` — `theories/foo.v` |")
    assert cells == ["Def 2.1", "A *precone* is a thing.", "`a`, `b` — `theories/foo.v`"]


def test_classifier_regression_anchor():
    flags = classify(
        paper_label="Thm 6.5",
        section_kind="paper",
        statement_html="dummy",
        regression_anchors=DEFAULT_REGRESSION_ANCHORS,
    )
    assert "axiom-free" in flags
    assert "regression-anchor" in flags


def test_classifier_gap():
    flags = classify(paper_label="§ 8", section_kind="gap", statement_html="")
    assert flags == ["gap"]


def test_classifier_discharged_deferred():
    flags = classify(
        paper_label="Lem X",
        section_kind="paper",
        statement_html="this previously-deferred follow-up was discharged",
    )
    assert "discharged-deferred" in flags


def test_parse_coqproject():
    project = ROOT.parent / "_CoqProject"
    bindings = parse_coqproject(project)
    assert any(b.physical == "theories" and b.logical == "Icones" for b in bindings)


def test_coqdoc_resolver_url():
    r = _resolver()
    url = r.coqdoc_url("theories/cones/precone.v")
    assert url == "docs/Icones.cones.precone.html"
    url = r.coqdoc_url("theories/homs/seely.v", anchor="ICones_Seely")
    assert url == "docs/Icones.homs.seely.html#ICones_Seely"
    assert r.coqdoc_url("not/a/known/path.v") is None


def test_coqdoc_resolver_github_url():
    r = _resolver(repo="LLM4Rocq/icones-rocq", commit="deadbeef")
    url = r.github_url("theories/cones/precone.v", line=12)
    assert url == "https://github.com/LLM4Rocq/icones-rocq/blob/deadbeef/theories/cones/precone.v#L12"


# -- golden-based parser tests ---------------------------------------------


@pytest.fixture
def parse_md(tmp_path):
    """Helper: parse a fixture and return the Document + warnings list."""

    def _parse(name: str, strict: bool = False):
        path = GOLDEN / name
        doc, warns = parse(
            path.read_text(encoding="utf-8"),
            resolver=_resolver(),
            project_root=tmp_path,  # off-disk so file-existence warnings DO trigger
            strict=strict,
        )
        return doc, warns

    return _parse


def test_simple_3col(parse_md):
    doc, _ = parse_md("01_simple_3col.md")
    assert len(doc.sections) == 1
    sec = doc.sections[0]
    assert sec.paper_section_number == "2"
    assert sec.title == "Cones"
    assert len(sec.entries) == 2
    ids = [e.id for e in sec.entries]
    assert ids == ["def-2-1", "def-2-2"]
    e = sec.entries[0]
    assert e.paper_kind == "Def"
    assert "axiom-free" in e.status
    assert e.detail is not None
    assert len(e.detail.snippets) == 1
    assert "precone" in e.rocq_idents
    assert any(f.path == "theories/cones/precone.v" for f in e.rocq_files)


def test_two_col_beyond(parse_md):
    doc, _ = parse_md("02_two_col_beyond.md")
    assert doc.sections == []
    assert len(doc.beyond) >= 1
    # Find the SAFT contrib.
    contrib = [c for c in doc.beyond if "SAFT" in c.title][0]
    assert len(contrib.entries) == 2
    assert all("beyond-paper" in e.status for e in contrib.entries)
    assert len(contrib.snippets) == 1


def test_h3_multiple_snippets(parse_md):
    doc, _ = parse_md("03_h3_multi_snippet.md")
    sec = doc.sections[0]
    e = sec.entries[0]
    assert e.detail is not None
    assert len(e.detail.snippets) == 2
    # The prose between snippets is captured.
    assert "Prose B" in e.detail.prose_html or "Prose A" in e.detail.prose_html


def test_blockquote_note(parse_md):
    doc, _ = parse_md("04_blockquote_note.md")
    sec = doc.sections[0]
    e = sec.entries[0]
    assert e.detail is not None
    assert len(e.detail.notes) == 1
    assert "Path note" in e.detail.notes[0].html


def test_beyond_cross_ref(parse_md):
    doc, _ = parse_md("05_beyond_cross_ref.md")
    sec = doc.sections[0]
    e = sec.entries[0]
    assert any(x.kind == "beyond" for x in e.cross_refs)


def test_gap_section(parse_md):
    doc, _ = parse_md("06_gap_section.md")
    # Gap rows go into doc.gaps, NOT into sections.
    assert doc.sections == []
    assert len(doc.gaps) == 2
    assert {g.paper_label for g in doc.gaps} == {"§ 8", "§ 10"}


def test_regression_anchor(parse_md):
    doc, _ = parse_md("07_regression_anchor.md")
    sec = doc.sections[0]
    e = sec.entries[0]
    assert "regression-anchor" in e.status
    assert "Thm 6.5" in doc.axiom_anchors.regression


def test_lem_range_slug(parse_md):
    doc, _ = parse_md("08_lem_range.md")
    sec = doc.sections[0]
    assert sec.entries[0].id == "lem-2-8-2-10"


def test_fuzzy_match_h3_via_idents(parse_md):
    """The §9 table row 'LL `!`' should match H3 'Linear exponential `!`'."""
    doc, _ = parse_md("09_fuzzy_match.md")
    sec = doc.sections[0]
    assert len(sec.entries) == 1
    e = sec.entries[0]
    assert e.paper_label == "LL `!`"
    assert e.detail is not None
    assert "Detail prose" in e.detail.prose_html or len(e.detail.snippets) == 1


def test_strict_warns_on_missing_file(parse_md):
    doc, warns = parse_md("01_simple_3col.md", strict=True)
    # No file actually on disk under tmp_path — strict should warn.
    assert any("not on disk" in w for w in warns)


def test_full_document_smoke():
    """Smoke test: parse the real docs/PAPER.md and assert plausible counts.

    Falls back to the legacy ``AUDITOR.md`` while the two-MD split is in
    flight (the orchestrator stream owns the actual content move).
    """
    paper_path = ROOT.parent / "docs" / "PAPER.md"
    legacy_path = ROOT.parent / "AUDITOR.md"
    src_path = paper_path if paper_path.is_file() else legacy_path
    if not src_path.is_file():
        pytest.skip("neither docs/PAPER.md nor AUDITOR.md present in this checkout")
    doc, _ = parse(
        src_path.read_text(encoding="utf-8"),
        resolver=_resolver(),
        project_root=ROOT.parent,
        strict=False,
    )
    # The document carries 7 paper-§ chapters and 3 gap rows.
    assert len(doc.sections) == 7
    assert len(doc.gaps) == 3
    n_entries = sum(len(s.entries) for s in doc.sections) + sum(
        len(b.entries) for b in doc.beyond
    )
    # Expected ballpark: ~80 entries.
    # Expected ~66 entries after AUDITOR.md → PAPER.md split (~80 legacy).
    assert 60 <= n_entries <= 120, f"got {n_entries}"
    # Regression anchor is present.
    assert any(
        "regression-anchor" in e.status for s in doc.sections for e in s.entries
    )


# -- snippet identifier cross-reference tests --------------------------------


def test_xref_ident_map(parse_md):
    """Map collects long-enough idents; short ones are excluded."""
    from tools.auditor.xref import MIN_IDENT_LEN, build_ident_map

    doc, _ = parse_md("12_xref.md")
    mapping = build_ident_map(doc)
    assert mapping["alpha_thing"] == "def-2-1"
    assert mapping["beta_gadget"] == "def-2-2"
    # `mu` (2 chars < MIN_IDENT_LEN) never enters the map.
    assert len("mu") < MIN_IDENT_LEN
    assert "mu" not in mapping


def test_xref_linkify(parse_md):
    """Cross-entry idents get anchors; self / unknown / short ones don't."""
    doc, _ = parse_md("12_xref.md")
    sec = doc.sections[0]
    a, b = sec.entries
    assert (a.id, b.id) == ("def-2-1", "def-2-2")
    a_html = a.detail.snippets[0].highlighted_html
    b_html = b.detail.snippets[0].highlighted_html
    # (a) an ident defined by entry A appearing in entry B's snippet gets
    # an anchor to A (and vice versa); href is tab-relative from a
    # depth-1 page.
    assert (
        '<a class="code-xref" href="../entries/def-2-1.html">alpha_thing</a>'
        in b_html
    )
    assert (
        '<a class="code-xref" href="../entries/def-2-2.html">beta_gadget</a>'
        in a_html
    )
    # (b) the self-occurrence in each entry's own snippet is NOT linked.
    assert '<span class="n">alpha_thing</span>' in a_html
    assert "entries/def-2-1.html" not in a_html
    assert '<span class="n">beta_gadget</span>' in b_html
    assert "entries/def-2-2.html" not in b_html
    # (c) an unknown ident gets no anchor.
    assert '<span class="n">unknown_zzz</span>' in a_html
    # (d) short idents (< MIN_IDENT_LEN) stay plain.
    assert '<span class="n">mu</span>' in a_html
    # (e) occurrences inside comment / string spans are never wrapped:
    # b's snippet mentions alpha_thing in a comment AND a string, but only
    # the name token carries an anchor.
    assert a_html.count("code-xref") == 1
    assert b_html.count("code-xref") == 1


def test_xref_linkify_idempotent(parse_md):
    """Running the linkify pass a second time changes nothing."""
    from tools.auditor.xref import linkify_document

    doc, _ = parse_md("12_xref.md")
    sec = doc.sections[0]
    before = [
        s.highlighted_html
        for e in sec.entries
        for s in (e.detail.snippets if e.detail else [])
    ]
    linkify_document(doc)
    after = [
        s.highlighted_html
        for e in sec.entries
        for s in (e.detail.snippets if e.detail else [])
    ]
    assert before == after


# -- two-tab orchestrator tests --------------------------------------------


def test_parse_two_tabs_basic(tmp_path):
    """Both tabs parsed; output is a ThreeTabDocument (Examples is empty)."""
    paper = GOLDEN / "01_simple_3col.md"
    ppl = GOLDEN / "02_two_col_beyond.md"
    two, warns = parse_two_tabs(
        paper_path=paper,
        ppl_path=ppl,
        resolver=_resolver(),
        project_root=tmp_path,
        strict=False,
    )
    # ``TwoTabDocument`` is a transitional alias for the new triple-tab shape.
    assert isinstance(two, ThreeTabDocument)
    assert isinstance(two, TwoTabDocument)
    # Paper tab carries a §2 section with two entries.
    assert len(two.paper.sections) == 1
    assert len(two.paper.sections[0].entries) == 2
    # PPL tab carries no §-sections; the new chapter-tree path materialises
    # at least one Chapter on PPL/Examples, and the compat shim mirrors
    # ``chapters[*].sections[*]`` into ``doc.beyond``.
    assert two.ppl.sections == []
    assert len(two.ppl.beyond) >= 1 and len(two.ppl.chapters) >= 1
    # Examples tab is the empty default when the legacy 2-arg shim is used.
    assert two.examples.sections == []
    assert two.examples.beyond == []
    # tab() helper round-trips.
    assert two.tab(TAB_PAPER) is two.paper
    assert two.tab(TAB_PPL) is two.ppl
    assert two.tab(TAB_EXAMPLES) is two.examples
    # Combined data.json export carries all three tabs.
    payload = two_tab_to_dict(two)
    assert set(payload) == {"paper", "ppl", "examples", "build_meta"}
    assert payload["paper"]["sections"][0]["id"].startswith("sec-")


def test_parse_two_tabs_strict_prefixes_warnings(tmp_path):
    """Strict warnings are prefixed with the tab they came from."""
    paper = GOLDEN / "01_simple_3col.md"
    ppl = GOLDEN / "02_two_col_beyond.md"
    two, warns = parse_two_tabs(
        paper_path=paper,
        ppl_path=ppl,
        resolver=_resolver(),
        project_root=tmp_path,  # off-disk → both tabs warn about missing files
        strict=True,
    )
    # Strict mode bails on the first failing tab — Paper goes first.
    assert any(w.startswith("[paper]") for w in warns)
    # PPL parse is skipped after the first failure under strict mode,
    # so the PPL document is the empty default.
    assert two.ppl.sections == [] and two.ppl.beyond == []


def test_parse_two_tabs_independent_status(tmp_path):
    """Statuses on Paper entries are not contaminated by PPL parsing."""
    paper = GOLDEN / "07_regression_anchor.md"  # contains Thm 6.5
    ppl = GOLDEN / "02_two_col_beyond.md"        # all beyond-paper
    two, _ = parse_two_tabs(
        paper_path=paper,
        ppl_path=ppl,
        resolver=_resolver(),
        project_root=tmp_path,
        strict=False,
    )
    # Paper retains its regression anchor.
    p_statuses = [
        s for sec in two.paper.sections for e in sec.entries for s in e.status
    ]
    assert "regression-anchor" in p_statuses
    # PPL contains only beyond-paper rows.  Iterate the chapter tree:
    # the chapter-mode build is the authoritative source on PPL/Examples.
    assert len(two.ppl.chapters) >= 1
    l_statuses = [
        s
        for c in two.ppl.chapters
        for sec in c.sections
        for e in sec.entries
        for s in e.status
    ]
    assert l_statuses and all(s == "beyond-paper" for s in l_statuses)


# -- three-tab orchestrator tests ------------------------------------------


def test_parse_three_tabs_basic(tmp_path):
    """All three tabs parsed independently; output is a ThreeTabDocument."""
    paper = GOLDEN / "01_simple_3col.md"
    ppl = GOLDEN / "02_two_col_beyond.md"
    examples = GOLDEN / "07_regression_anchor.md"
    three, warns = parse_three_tabs(
        paper_path=paper,
        ppl_path=ppl,
        examples_path=examples,
        resolver=_resolver(),
        project_root=tmp_path,
        strict=False,
    )
    assert isinstance(three, ThreeTabDocument)
    # Paper tab: §2 with two entries.
    assert len(three.paper.sections) == 1
    assert len(three.paper.sections[0].entries) == 2
    # PPL tab: chapter-tree path active.  Compat shim mirrors the chapter
    # tree onto ``doc.beyond`` so the legacy ``len(beyond) >= 1`` check
    # still holds.
    assert three.ppl.sections == []
    assert len(three.ppl.beyond) >= 1 and len(three.ppl.chapters) >= 1
    # Examples tab: regression-anchor fixture has a paper section.
    assert len(three.examples.sections) == 1
    # tab() round-trips for all three names.
    assert three.tab(TAB_PAPER) is three.paper
    assert three.tab(TAB_PPL) is three.ppl
    assert three.tab(TAB_EXAMPLES) is three.examples
    # Combined export carries all three tabs.
    payload = three_tab_to_dict(three)
    assert set(payload) == {"paper", "ppl", "examples", "build_meta"}


def test_parse_three_tabs_prefixes_warnings(tmp_path):
    """Strict warnings get prefixed with the tab they came from."""
    paper = GOLDEN / "01_simple_3col.md"
    ppl = GOLDEN / "02_two_col_beyond.md"
    examples = GOLDEN / "07_regression_anchor.md"
    _, warns = parse_three_tabs(
        paper_path=paper,
        ppl_path=ppl,
        examples_path=examples,
        resolver=_resolver(),
        project_root=tmp_path,  # off-disk → missing-file warnings fire
        strict=True,
    )
    # Strict mode aborts on the first failing tab → Paper is the first.
    assert any(w.startswith("[paper]") for w in warns)
    by_tab = {tab: sum(1 for w in warns if w.startswith(f"[{tab}]"))
              for tab in ALL_TABS}
    assert by_tab["paper"] > 0
    # Ppl + examples may carry zero file refs in these fixtures, in which
    # case their prefixes won't fire — that's fine: the test only checks
    # the prefix machinery itself surfaces correctly for the Paper tab.


# -- chapter-tree tests (PPL / Examples) -----------------------------------


def test_ppl_chapter_section_shape_b(tmp_path):
    """PPL-shape fixture: H3 with prose + snippets and no headline table."""
    path = GOLDEN / "10_ppl_chapter_section.md"
    doc, _ = parse(
        path.read_text(encoding="utf-8"),
        resolver=_resolver(),
        project_root=tmp_path,
        strict=False,
        tab=TAB_PPL,
    )
    assert len(doc.chapters) == 1
    ch = doc.chapters[0]
    assert ch.id.startswith("ppl-ch-")
    # Two H3s in the fixture → two sections.
    assert len(ch.sections) == 2
    # Shape (b): single-Entry section with id == section.id.
    for sec in ch.sections:
        assert len(sec.entries) == 1
        assert sec.entries[0].id == sec.id
        assert sec.entries[0].detail is not None
        # Each H3 fixture carries one Coq snippet inlined into the entry detail.
        assert len(sec.entries[0].detail.snippets) >= 1
    # Chapter stats roll up sensibly.
    assert ch.stats.n_sections == 2
    assert ch.stats.n_entries == 2
    assert ch.stats.loc > 0
    # Compat shim populates ``doc.beyond``.
    assert len(doc.beyond) >= 1


def test_examples_overview_table_shape_c(tmp_path):
    """EXAMPLES-shape fixture: H3 with a Paper-style overview table.

    One entry per table row; the leftmost label carries the kind
    (``Def`` / ``Thm`` / ``Lem``, paper number optional), and each
    row's identifiers are matched against the section's snippets to
    populate the entry's foldable detail.  The fixture's H2 has no
    "Beyond the paper" prefix — chapter mode treats every plain H2 as
    a chapter.
    """
    path = GOLDEN / "11_examples_headline_table.md"
    doc, _ = parse(
        path.read_text(encoding="utf-8"),
        resolver=_resolver(),
        project_root=tmp_path,
        strict=False,
        tab=TAB_EXAMPLES,
    )
    assert len(doc.chapters) == 1
    ch = doc.chapters[0]
    assert ch.id.startswith("examples-ch-")
    assert len(ch.sections) == 1
    sec = ch.sections[0]
    # 3 overview-table rows → 3 entries.
    assert len(sec.entries) == 3
    # Position 0 = the program entry (Definition ex_geom).
    prog = sec.entries[0]
    assert prog.paper_kind == "Def"
    assert prog.paper_number is None
    assert prog.rocq_idents == ["ex_geom"]
    assert prog.detail is not None
    assert len(prog.detail.snippets) == 1
    assert (
        prog.detail.snippets[0].source_file
        == "theories/programs/examples.v"
    )
    # Position 1 = the mass theorem; the matched snippet is the one
    # whose source_file is em_fix_arr.v (it declares
    # `Theorem ex_geom_arr_mass_one`).
    e1 = sec.entries[1]
    assert e1.rocq_idents == ["ex_geom_arr_mass_one"]
    assert e1.paper_kind == "Thm"
    assert e1.detail is not None
    assert e1.detail.snippets
    assert (
        e1.detail.snippets[0].source_file
        == "theories/programs/infra/em_fix_arr.v"
    )
    # Position 2 = the structural lemma.
    assert sec.entries[2].paper_kind == "Lem"
    # Stats roll up.
    assert ch.stats.n_entries == 3
    assert ch.stats.n_defs == 1
    assert ch.stats.n_thms == 2
    assert ch.stats.loc > 0
    # Section-level snippets list is empty — every H3 snippet got
    # hoisted into an entry's detail.  This is what lets the section
    # template skip the standalone ``<section class="snippets">``
    # block at the top.
    assert sec.snippets == []


def test_parse_tabs_generic_orchestrator(tmp_path):
    """parse_tabs accepts a dict and rejects missing keys."""
    srcs = {
        TAB_PAPER: GOLDEN / "01_simple_3col.md",
        TAB_PPL: GOLDEN / "02_two_col_beyond.md",
        TAB_EXAMPLES: GOLDEN / "07_regression_anchor.md",
    }
    three, _ = parse_tabs(
        srcs, resolver=_resolver(), project_root=tmp_path, strict=False
    )
    assert isinstance(three, ThreeTabDocument)
    assert len(three.examples.sections) == 1
    # Missing key raises.
    incomplete = {TAB_PAPER: srcs[TAB_PAPER], TAB_PPL: srcs[TAB_PPL]}
    import pytest as _pt
    with _pt.raises(KeyError):
        parse_tabs(
            incomplete,
            resolver=_resolver(),
            project_root=tmp_path,
            strict=False,
        )
