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
    parse_two_tabs,
    slugify_label,
    _classify_paper_label_kind,  # noqa: PLC2701 — tested intentionally
    _split_table_row,  # noqa: PLC2701
)
from tools.auditor.schema import TAB_PAPER, TAB_PPL, TwoTabDocument, two_tab_to_dict


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


# -- two-tab orchestrator tests --------------------------------------------


def test_parse_two_tabs_basic(tmp_path):
    """Both tabs parsed independently; output is a TwoTabDocument."""
    paper = GOLDEN / "01_simple_3col.md"
    ppl = GOLDEN / "02_two_col_beyond.md"
    two, warns = parse_two_tabs(
        paper_path=paper,
        ppl_path=ppl,
        resolver=_resolver(),
        project_root=tmp_path,
        strict=False,
    )
    assert isinstance(two, TwoTabDocument)
    # Paper tab carries a §2 section with two entries.
    assert len(two.paper.sections) == 1
    assert len(two.paper.sections[0].entries) == 2
    # PPL tab carries no §-sections but at least one Beyond contrib.
    assert two.ppl.sections == []
    assert len(two.ppl.beyond) >= 1
    # tab() helper round-trips.
    assert two.tab(TAB_PAPER) is two.paper
    assert two.tab(TAB_PPL) is two.ppl
    # Combined data.json export carries both tabs.
    payload = two_tab_to_dict(two)
    assert set(payload) == {"paper", "ppl", "build_meta"}
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
    # PPL contains only beyond-paper rows.
    l_statuses = [
        s for b in two.ppl.beyond for e in b.entries for s in e.status
    ]
    assert l_statuses and all(s == "beyond-paper" for s in l_statuses)
