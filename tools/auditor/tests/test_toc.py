"""Tests for the table-of-contents sidebar (``tools.auditor.toc`` + render).

The sidebar shows the full site hierarchy on every page.  These tests check
the TOC tree is well-formed (3 tabs, correct nesting, kind/url fields), that
every node ``url`` resolves to an emitted file after a real render, that the
active node is marked on a sample page, and that all 3 tabs appear on every
page type.
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

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
    Section,
    ThreeTabDocument,
)
from tools.auditor.toc import build_toc


def _entry(eid: str) -> Entry:
    return Entry(
        id=eid,
        paper_label=eid,
        paper_kind="Def",
        paper_number=None,
        paper_section_id="sec-x",
        statement_html="",
        rocq_idents=[],
        rocq_files=[],
        status=["axiom-free"],
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


def _beyond(bid: str, entries) -> BeyondContrib:
    return BeyondContrib(id=bid, title=bid, intro_html="", entries=list(entries))


def _chapter(cid: str, sections) -> Chapter:
    return Chapter(
        id=cid,
        title=cid,
        intro_html="",
        sections=list(sections),
        stats=ChapterStats(),
    )


def _sample_three() -> ThreeTabDocument:
    """A small but structurally complete triple-tab doc.

    Paper: §-sections + a Beyond contribution (legacy tree).
    PPL / Examples: chapter → section → entry tree.
    """
    paper = Document(preamble_html="")
    paper.sections = [
        _section("sec-2", [_entry("def-2-1"), _entry("def-2-2")], num="2"),
    ]
    paper.beyond = [_beyond("b-saft", [_entry("saft-thm")])]

    ppl = Document(preamble_html="")
    ppl.chapters = [
        _chapter("ppl-ch-1", [_section("ppl-sec-1", [_entry("ppl-e-1")], chapter_id="ppl-ch-1")]),
    ]

    examples = Document(preamble_html="")
    examples.chapters = [
        _chapter("ex-ch-1", [_section("ex-sec-1", [_entry("ex-e-1")], chapter_id="ex-ch-1")]),
    ]
    return ThreeTabDocument(paper=paper, ppl=ppl, examples=examples)


# -- tree shape -------------------------------------------------------------


def test_build_toc_three_tabs_in_order():
    toc = build_toc(_sample_three())
    assert [n["id"] for n in toc] == ["paper", "ppl", "examples"]
    assert all(n["kind"] == "tab" for n in toc)
    assert [n["title"] for n in toc] == ["Paper", "PPL", "Examples"]


def test_build_toc_paper_nesting():
    toc = build_toc(_sample_three())
    paper = toc[0]
    kinds = [c["kind"] for c in paper["children"]]
    # a §-section then a Beyond contribution
    assert kinds == ["section", "beyond"]
    sec = paper["children"][0]
    assert sec["id"] == "sec-2"
    assert sec["url"] == "paper/sections/sec-2.html"
    assert [e["kind"] for e in sec["children"]] == ["entry", "entry"]
    assert sec["children"][0]["url"] == "paper/entries/def-2-1.html"
    beyond = paper["children"][1]
    assert beyond["url"] == "paper/beyond/b-saft.html"


def test_build_toc_chapter_nesting():
    toc = build_toc(_sample_three())
    ppl = toc[1]
    assert [c["kind"] for c in ppl["children"]] == ["chapter"]
    ch = ppl["children"][0]
    assert ch["url"] == "ppl/chapters/ppl-ch-1.html"
    sec = ch["children"][0]
    assert sec["kind"] == "section" and sec["url"] == "ppl/sections/ppl-sec-1.html"
    # ppl-sec-1's lone entry has a DISTINCT id (ppl-e-1), so it is NOT
    # collapsed: the entry child is kept.
    assert sec["children"][0]["url"] == "ppl/entries/ppl-e-1.html"


def _canonical_three() -> ThreeTabDocument:
    """A triple-tab doc whose PPL section wraps ONE entry with id==section.id.

    This is the synthetic single-entry shape the parser emits for a
    table-less PPL/Examples H3: the section page is canonical and inlines
    the entry, so the standalone entry page/node/link is suppressed.
    """
    paper = Document(preamble_html="")
    ppl = Document(preamble_html="")
    ppl.chapters = [
        _chapter(
            "ppl-ch-1",
            [
                _section(
                    "ppl-sec-solo",
                    [_entry("ppl-sec-solo")],  # id == section.id
                    chapter_id="ppl-ch-1",
                ),
            ],
        ),
    ]
    examples = Document(preamble_html="")
    return ThreeTabDocument(paper=paper, ppl=ppl, examples=examples)


def test_canonical_single_entry_section_has_no_entry_child():
    """A section whose lone entry has id==section.id drops the entry child."""
    toc = build_toc(_canonical_three())
    ppl = toc[1]
    sec = ppl["children"][0]["children"][0]
    assert sec["kind"] == "section"
    assert sec["id"] == "ppl-sec-solo"
    assert sec["children"] == []


def test_canonical_single_entry_section_page_is_canonical(tmp_path):
    """The section page exists; the redundant entry page is NOT emitted."""
    three = _canonical_three()
    render(three, tmp_path)
    assert (tmp_path / "ppl/sections/ppl-sec-solo.html").exists()
    assert not (tmp_path / "ppl/entries/ppl-sec-solo.html").exists()


def _walk_urls(nodes):
    for n in nodes:
        if n.get("url"):
            yield n["url"]
        yield from _walk_urls(n["children"])


# -- rendered output --------------------------------------------------------


def test_all_node_urls_resolve_after_render(tmp_path):
    """Every TOC node url points at a file emitted by ``render``."""
    three = _sample_three()
    render(three, tmp_path)
    for url in _walk_urls(build_toc(three)):
        assert (tmp_path / url).exists(), f"TOC url has no emitted file: {url}"


def test_sidebar_present_with_three_tabs_on_every_page_type(tmp_path):
    three = _sample_three()
    render(three, tmp_path)
    pages = [
        "index.html",
        "graph.html",
        "paper/index.html",
        "paper/sections/sec-2.html",
        "paper/entries/def-2-1.html",
        "paper/beyond/b-saft.html",
        "paper/gaps.html",
        "ppl/index.html",
        "ppl/chapters/ppl-ch-1.html",
        "ppl/sections/ppl-sec-1.html",
        "examples/entries/ex-e-1.html",
    ]
    for p in pages:
        html = (tmp_path / p).read_text(encoding="utf-8")
        assert 'class="toc-sidebar"' in html, f"sidebar missing on {p}"
        for t in ("toc-tab-paper", "toc-tab-ppl", "toc-tab-examples"):
            assert t in html, f"{t} missing on {p}"


def test_active_node_marked_on_entry_page(tmp_path):
    three = _sample_three()
    render(three, tmp_path)
    html = (tmp_path / "paper/entries/def-2-1.html").read_text(encoding="utf-8")
    # exactly one active sidebar link, and it points at this entry
    links = re.findall(
        r'<a class="toc-link[^"]*" href="([^"]+)"[^>]*aria-current="true"', html
    )
    assert links == ["../../paper/entries/def-2-1.html"]


def test_active_branch_auto_expanded_on_section_page(tmp_path):
    """The active section's ancestor chapter <details> is rendered open."""
    three = _sample_three()
    render(three, tmp_path)
    html = (tmp_path / "ppl/sections/ppl-sec-1.html").read_text(encoding="utf-8")
    # the ppl tab fold carries the active branch marker and is open
    assert "toc-tab toc-tab-ppl is-active-branch" in html
    # the active section link is marked
    assert 'aria-current="true"' in html


def test_toc_links_resolve_from_deep_page(tmp_path):
    """Every sidebar link on a depth-2 entry page resolves to a real file."""
    three = _sample_three()
    render(three, tmp_path)
    page = "paper/entries/def-2-1.html"
    html = (tmp_path / page).read_text(encoding="utf-8")
    base = os.path.dirname(page)
    hrefs = re.findall(r'class="toc-(?:link|tab-link)[^"]*" href="([^"]+)"', html)
    assert hrefs, "no toc links found"
    for href in hrefs:
        target = os.path.normpath(os.path.join(base, href.split("#")[0]))
        assert (tmp_path / target).exists(), f"dangling toc link {href} -> {target}"
