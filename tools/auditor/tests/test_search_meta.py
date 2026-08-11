"""Tests for the Pagefind search metadata emitted by the UI templates.

The search index is built from ``data-pagefind-meta`` (the pills shown under
a search result) and ``data-pagefind-filter`` (the filter checkboxes) found
in the rendered HTML.  What lands there is a *curation* decision, and this
module pins it:

* a tag must DISTINGUISH a result.  ``axiom-free`` holds for the whole
  development (zero Axiom/Admitted), so it is never indexed; ``beyond-paper``
  is the definition of the PPL and Examples tabs, so it is indexed on the
  Paper tab only, where it separates the entries with no paper counterpart;
  ``gap`` / ``regression-anchor`` are rare, hence always indexed.
* provenance is exactly ONE tab pill per page — Pagefind meta is page-level,
  so a per-card tag would silently keep whichever card rendered last.
* markers carry their value in the attribute and stay EMPTY: a marker with
  text has that text indexed as page content and reused as the element's
  anchor label (the "beyond-paperppl" prefix that used to open every PPL
  excerpt).

Everything is asserted against a real ``render`` of a synthetic three-tab
document, so the templates, not a reimplementation of them, are under test.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT.parent) not in sys.path:
    sys.path.insert(0, str(ROOT.parent))

from tools.auditor.render import render
from tools.auditor.schema import (
    BeyondContrib,
    Chapter,
    ChapterStats,
    Document,
    Entry,
    GapEntry,
    Section,
    ThreeTabDocument,
)


# -- fixtures ---------------------------------------------------------------


def _entry(eid: str, status: list[str]) -> Entry:
    return Entry(
        id=eid,
        paper_label=eid,
        paper_kind="Def",
        paper_number=None,
        paper_section_id="sec-x",
        statement_html="<p>Statement.</p>",
        rocq_idents=[],
        rocq_files=[],
        status=list(status),
        detail=None,
    )


def _section(sid: str, entries, *, num="", chapter_id="") -> Section:
    return Section(
        id=sid,
        paper_section=f"§ {sid}",
        paper_section_number=num,
        title=sid,
        intro_html="",
        entries=list(entries),
        chapter_id=chapter_id,
    )


def _three() -> ThreeTabDocument:
    """One document exercising every status × tab combination that exists.

    Paper: a §-section holding the everyday ``axiom-free`` entry, a
    ``regression-anchor`` one and a paper-tab ``beyond-paper`` one, plus a
    Beyond contribution and a declared gap.
    PPL: the same legacy shape (sections + Beyond contribs), so ``beyond.html``
    is exercised off the Paper tab too.
    Examples: the chapter → section → entry tree.
    Every PPL/Examples entry is ``beyond-paper`` — that is what those tabs
    mean, which is precisely why it must not be indexed there.
    """
    paper = Document(preamble_html="")
    paper.sections = [
        _section(
            "sec-2",
            [
                _entry("def-2-1", ["axiom-free"]),
                _entry("thm-2-2", ["axiom-free", "regression-anchor"]),
                _entry("def-2-3", ["beyond-paper"]),
            ],
            num="2",
        ),
    ]
    paper.beyond = [BeyondContrib(id="b-saft", title="SAFT", intro_html="",
                                  entries=[_entry("saft-thm", ["beyond-paper"])],
                                  stats=ChapterStats())]
    paper.gaps = [GapEntry(id="gap-9", paper_label="§ 9",
                           description_html="<p>Not done.</p>", reason_html="")]

    # Legacy shape (no chapters) — render then emits the ppl/beyond/ tree.
    ppl = Document(preamble_html="")
    ppl.sections = [_section("ppl-sec-1", [_entry("ppl-e-1", ["beyond-paper"])])]
    ppl.beyond = [BeyondContrib(id="ppl-b-1", title="Grammar", intro_html="",
                                entries=[_entry("ppl-b-e", ["beyond-paper"])],
                                stats=ChapterStats())]

    examples = Document(preamble_html="")
    examples.chapters = [
        Chapter(
            id="ex-ch-1",
            title="Rejection",
            intro_html="",
            sections=[_section("ex-sec-1", [_entry("ex-e-1", ["beyond-paper"])],
                               chapter_id="ex-ch-1")],
            stats=ChapterStats(),
        ),
    ]
    return ThreeTabDocument(paper=paper, ppl=ppl, examples=examples)


@pytest.fixture(scope="module")
def site(tmp_path_factory) -> Path:
    out = tmp_path_factory.mktemp("site")
    render(_three(), out)
    return out


def _html(site: Path, rel: str) -> str:
    return (site / rel).read_text(encoding="utf-8")


def _pages(site: Path) -> list[Path]:
    return sorted(site.rglob("*.html"))


_FILTER_RE = re.compile(r'data-pagefind-filter="([^"]*)"')
_META_RE = re.compile(r'data-pagefind-meta="([^"]*)"')


def _filters(html: str) -> list[str]:
    return _FILTER_RE.findall(html)


def _metas(html: str) -> list[str]:
    return _META_RE.findall(html)


# -- the status policy ------------------------------------------------------


def test_axiom_free_never_reaches_the_search_index(site):
    """Zero axioms repo-wide ⇒ the status distinguishes nothing."""
    for page in _pages(site):
        html = page.read_text(encoding="utf-8")
        offenders = [v for v in _filters(html) + _metas(html) if "axiom-free" in v]
        assert not offenders, f"{page.name} still indexes axiom-free: {offenders}"


def test_axiom_free_entry_contributes_no_status_filter(site):
    """An everyday entry adds nothing: its page is findable, not tagged."""
    html = _html(site, "paper/entries/def-2-1.html")
    assert [v for v in _filters(html) if v.startswith("status:")] == []
    assert [v for v in _metas(html) if v.startswith("status:")] == []


def test_gap_is_always_indexed(site):
    html = _html(site, "paper/gaps.html")
    assert "status:gap" in _filters(html)
    assert "status:gap" in _metas(html)


def test_regression_anchor_is_always_indexed(site):
    html = _html(site, "paper/entries/thm-2-2.html")
    assert "status:regression-anchor" in _filters(html)
    assert "status:regression-anchor" in _metas(html)
    # …and it travels with the entry onto its section page.
    assert "status:regression-anchor" in _filters(_html(site, "paper/sections/sec-2.html"))


@pytest.mark.parametrize(
    "page",
    ["paper/entries/def-2-3.html", "paper/beyond/b-saft.html",
     "paper/sections/sec-2.html"],
)
def test_beyond_paper_is_indexed_on_the_paper_tab(site, page):
    """There it separates the entries with no paper counterpart."""
    assert "status:beyond-paper" in _filters(_html(site, page))


@pytest.mark.parametrize(
    "page",
    ["ppl/entries/ppl-e-1.html", "ppl/sections/ppl-sec-1.html",
     "ppl/beyond/ppl-b-1.html", "examples/entries/ex-e-1.html",
     "examples/sections/ex-sec-1.html"],
)
def test_beyond_paper_is_not_indexed_off_the_paper_tab(site, page):
    """On PPL/Examples every entry has it — it would just repeat the tab."""
    html = _html(site, page)
    assert [v for v in _filters(html) if "beyond-paper" in v] == []
    assert [v for v in _metas(html) if "beyond-paper" in v] == []


# -- provenance -------------------------------------------------------------


@pytest.mark.parametrize(
    ("page", "label", "slug"),
    [
        ("paper/index.html", "Paper", "paper"),
        ("paper/sections/sec-2.html", "Paper", "paper"),
        ("paper/entries/def-2-1.html", "Paper", "paper"),
        ("ppl/entries/ppl-e-1.html", "PPL", "ppl"),
        ("examples/entries/ex-e-1.html", "Examples", "examples"),
    ],
)
def test_exactly_one_tab_pill_and_filter_per_page(site, page, label, slug):
    html = _html(site, page)
    assert [v for v in _metas(html) if v.startswith("tab:")] == [f"tab:{label}"]
    assert [v for v in _filters(html) if v.startswith("tab:")] == [f"tab:{slug}"]


def test_one_status_pill_at_most_per_page(site):
    """Pagefind meta is page-level: a second one would silently overwrite."""
    for page in _pages(site):
        html = page.read_text(encoding="utf-8")
        status_pills = [v for v in _metas(html) if v.startswith("status:")]
        assert len(status_pills) <= 1, f"{page.name}: {status_pills}"


def test_mixed_pages_carry_no_status_pill(site):
    """A section page holds several statuses — none of them is *the* page's."""
    html = _html(site, "paper/sections/sec-2.html")
    assert [v for v in _metas(html) if v.startswith("status:")] == []


# -- shape of the emitted attributes ----------------------------------------


def test_every_marker_declares_a_single_key(site):
    """Pagefind does not split on commas: "a:x, b:y" indexes ONE key `a`
    whose value is "x, b:y" (which is how `status` came to hold values like
    "beyond-paper, tab:ppl")."""
    for page in _pages(site):
        html = page.read_text(encoding="utf-8")
        for value in _filters(html) + _metas(html):
            assert "," not in value, f"{page.name}: multi-key attribute {value!r}"
            assert value.count(":") == 1, f"{page.name}: malformed {value!r}"


def test_markers_carry_their_value_in_the_attribute_not_as_text(site):
    """A marker with text pollutes the indexed content and the anchor label."""
    marker = re.compile(r"<span\b[^>]*\bdata-pagefind-(?:meta|filter)=[^>]*>(.*?)</span>",
                        re.S)
    for page in _pages(site):
        for text in marker.findall(page.read_text(encoding="utf-8")):
            assert text.strip() == "", f"{page.name}: marker has text {text!r}"


def test_no_filter_or_meta_key_without_a_value(site):
    """The bare-key form (`data-pagefind-filter="status"`) takes its value
    from the element text, which is exactly what we do not want."""
    for page in _pages(site):
        html = page.read_text(encoding="utf-8")
        for value in _filters(html) + _metas(html):
            key, _, val = value.partition(":")
            assert key.strip() and val.strip(), f"{page.name}: {value!r}"
