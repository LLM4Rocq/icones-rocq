"""Tests for the assistant-bundle generator (``tools.auditor.skillgen``).

``skillgen`` consumes ONLY a site's already-built ``graph.json`` /
``data.json`` (never re-parses markdown or ``.v`` sources) plus a set of
text templates, and derives ``<site>/assistant/`` — an Agent Skill zip, its
unpacked ``skill/`` tree, a self-contained chat widget and a landing page.
These tests build a small but realistic ``graph.json``/``data.json`` pair
and a minimal set of stand-in templates entirely under ``tmp_path`` (the
real templates under ``tools/auditor/assistant/`` are authored separately
and may not exist yet), then check the generator's outputs against that
fixture.
"""

from __future__ import annotations

import json
import re
import sys
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT.parent) not in sys.path:
    sys.path.insert(0, str(ROOT.parent))

import pytest

from tools.auditor.skillgen import generate_assistant_bundle

COMMIT = "abcdef0123456789abcdef0123456789abcdef01"
LONG_STATEMENT = "<p>" + ("word " * 200) + "</p>"  # well over 600 chars of text


# ---------------------------------------------------------------------------
# Fixture builders
# ---------------------------------------------------------------------------


def _write_graph_json(site_dir: Path) -> None:
    nodes = [
        {
            "data": {
                "id": "tab::paper",
                "ntype": "tab",
                "tab": "paper",
                "label": "Paper",
            }
        },
        {
            "data": {
                "id": "grp::paper::sec-7",
                "ntype": "group",
                "tab": "paper",
                "label": "§ 7 — Stable cones",
            }
        },
        {
            "data": {
                "id": "paper::lem-7-16",
                "ntype": "entry",
                "tab": "paper",
                "parent": "grp::paper::sec-7",
                "label": "Lem 7.16",
                "kind": "Lem",
                "status": ["axiom-free"],
                "idents": ["is_n_increasing_Delta"],
                "files": ["theories/stable/findiff.v"],
                "group_label": "§ 7 — Stable cones",
                "url": "paper/entries/lem-7-16.html",
                "leaf": False,
                "root": False,
                "isolated": False,
            }
        },
        {
            "data": {
                "id": "paper::def-7-15",
                "ntype": "entry",
                "tab": "paper",
                "parent": "grp::paper::sec-7",
                "label": "Def 7.15",
                "kind": "Def",
                "status": ["axiom-free", "beyond-paper"],
                "idents": ["n_increasing"],
                "files": ["theories/stable/findiff.v"],
                "group_label": "§ 7 — Stable cones",
                "url": "paper/entries/def-7-15.html",
                "leaf": True,
                "root": False,
                "isolated": False,
            }
        },
        {
            "data": {
                "id": "ppl::thm-surface-1",
                "ntype": "entry",
                "tab": "ppl",
                "parent": "grp::ppl::sec-surface",
                "label": "Thm S.1",
                "kind": "Thm",
                "status": ["axiom-free"],
                "idents": ["surface_sound"],
                "files": ["theories/programs/surface.v"],
                "group_label": "The surface language",
                "url": "ppl/entries/thm-surface-1.html",
                "leaf": True,
                "root": True,
                "isolated": True,
            }
        },
    ]
    edges = [
        {
            "data": {
                "id": "e0",
                "source": "paper::lem-7-16",
                "target": "paper::def-7-15",
                "kind": "depends",
                "directed": True,
            }
        },
        {
            "data": {
                "id": "e1",
                "source": "paper::lem-7-16",
                "target": "ppl::thm-surface-1",
                "kind": "mentions",
                "directed": False,
            }
        },
    ]
    meta = {
        "n_entries": 3,
        "n_depends": 1,
        "n_mentions": 1,
        "n_leaves": 1,
        "n_refs_stmt": 4,
        "n_refs_proof": 2,
    }
    payload = {"nodes": nodes, "edges": edges, "meta": meta}
    (site_dir / "graph.json").write_text(json.dumps(payload), encoding="utf-8")


def _entry_dict(
    eid: str,
    label: str,
    kind: str,
    statement_html: str,
    idents: list[str],
    files: list[str],
    status: list[str],
) -> dict:
    return {
        "id": eid,
        "paper_label": label,
        "paper_kind": kind,
        "paper_number": None,
        "paper_section_id": "sec-7",
        "statement_html": statement_html,
        "rocq_idents": idents,
        "rocq_files": [
            {
                "path": f,
                "section": None,
                "github_url": "",
                "coqdoc_url": None,
                "coqdoc_anchor": None,
            }
            for f in files
        ],
        "status": status,
        "detail": None,
        "cross_refs": [],
    }


def _write_data_json(site_dir: Path) -> None:
    paper = {
        "preamble_html": "",
        "sections": [
            {
                "id": "sec-7",
                "paper_section": "§ 7",
                "paper_section_number": "7",
                "title": "Stable cones",
                "intro_html": "",
                "entries": [
                    _entry_dict(
                        "lem-7-16",
                        "Lem 7.16",
                        "Lem",
                        "<em>x &amp; y</em> is Delta-increasing.",
                        ["is_n_increasing_Delta"],
                        ["theories/stable/findiff.v"],
                        ["axiom-free"],
                    ),
                    _entry_dict(
                        "def-7-15",
                        "Def 7.15",
                        "Def",
                        LONG_STATEMENT,
                        ["n_increasing"],
                        ["theories/stable/findiff.v"],
                        ["axiom-free", "beyond-paper"],
                    ),
                ],
                "notes_html": "",
                "chapter_id": "",
                "snippets": [],
                "overview": [],
                "stats": {},
            }
        ],
        "chapters": [],
        "beyond": [],
        "gaps": [
            {
                "id": "gap-1",
                "paper_label": "§ 9",
                "description_html": "<p>Fubini for <b>mixed</b> measures.</p>",
                "reason_html": "<p>Out of scope &amp; deferred.</p>",
            }
        ],
        "verify_instructions_html": "<p>Run <code>make verify</code>.</p>",
        "axiom_anchors": {
            "regression": "No new axioms beyond the regression set.",
            "headlines": ["Lem 7.16 is axiom-free."],
        },
        "build_meta": {"commit": COMMIT, "built_at": "2026-09-07T00:00:00+00:00", "auditor_lines": 42},
    }
    ppl = {
        "preamble_html": "",
        "sections": [],
        "chapters": [
            {
                "id": "ppl-ch-surface",
                "title": "The surface language",
                "intro_html": "",
                "sections": [
                    {
                        "id": "sec-surface",
                        "paper_section": "",
                        "paper_section_number": "",
                        "title": "The surface language",
                        "intro_html": "",
                        "entries": [
                            _entry_dict(
                                "thm-surface-1",
                                "Thm S.1",
                                "Thm",
                                "<p>Surface soundness.</p>",
                                ["surface_sound"],
                                ["theories/programs/surface.v"],
                                ["axiom-free"],
                            )
                        ],
                        "notes_html": "",
                        "chapter_id": "ppl-ch-surface",
                        "snippets": [],
                        "overview": [],
                        "stats": {},
                    }
                ],
                "notes_html": "",
                "stats": {},
                "overview": [],
            }
        ],
        "beyond": [],
        "gaps": [],
        "verify_instructions_html": "<p>Run <code>make ppl-verify</code>.</p>",
        "axiom_anchors": {"regression": "", "headlines": []},
        "build_meta": {"commit": COMMIT, "built_at": "2026-09-07T00:00:00+00:00", "auditor_lines": 10},
    }
    examples = {
        "preamble_html": "",
        "sections": [],
        "chapters": [],
        "beyond": [],
        "gaps": [],
        "verify_instructions_html": "",
        "axiom_anchors": {"regression": "", "headlines": []},
        "build_meta": {"commit": COMMIT, "built_at": "2026-09-07T00:00:00+00:00", "auditor_lines": 0},
    }
    payload = {
        "paper": paper,
        "ppl": ppl,
        "examples": examples,
        "build_meta": {"commit": COMMIT, "built_at": "2026-09-07T00:00:00+00:00", "auditor_lines": 52},
    }
    (site_dir / "data.json").write_text(json.dumps(payload), encoding="utf-8")


def _write_site_fixture(site_dir: Path) -> None:
    site_dir.mkdir(parents=True, exist_ok=True)
    _write_graph_json(site_dir)
    _write_data_json(site_dir)


def _write_templates(template_dir: Path, *, typo: bool = False) -> None:
    template_dir.mkdir(parents=True, exist_ok=True)
    typo_marker = "{{TYPO_KEY}}\n" if typo else ""
    (template_dir / "skill_header.md.in").write_text(
        "---\n"
        "name: icones-audit\n"
        "---\n"
        f"# Icones audit skill ({{{{N_ENTRIES}}}} entries, commit {{{{COMMIT}}}})\n"
        f"{typo_marker}",
        encoding="utf-8",
    )
    (template_dir / "core_guide.md.in").write_text(
        "## Core guide\n"
        "Site: {{SITE}}\n"
        "Status distribution:\n"
        "{{STATUS_COUNTS}}\n"
        "{{TAB_COUNTS}}\n"
        "Artifact: {{ARTIFACT_URL}}\n",
        encoding="utf-8",
    )
    (template_dir / "chat_header.md.in").write_text(
        "# Chat rules\nCommit {{COMMIT}} at {{SITE}}\n",
        encoding="utf-8",
    )
    (template_dir / "landing.html.in").write_text(
        "<title>Icones audit assistant</title>\n"
        "<p>Skill zip: <a href=\"{{SKILL_ZIP_URL}}\">download</a></p>\n"
        "<p>Entries: {{N_ENTRIES}} · Commit {{COMMIT}}</p>\n",
        encoding="utf-8",
    )
    (template_dir / "chatbot.html.in").write_text(
        "<title>Icones audit chat</title>\n"
        "<p>Built at commit {{COMMIT}}</p>\n"
        "<script>\n"
        "const DATA = __CHATDATA_JSON__;\n"
        "const RULES = __CHAT_RULES_JSON__;\n"
        "</script>\n",
        encoding="utf-8",
    )


@pytest.fixture
def site(tmp_path: Path) -> Path:
    site_dir = tmp_path / "site"
    _write_site_fixture(site_dir)
    return site_dir


@pytest.fixture
def templates(tmp_path: Path) -> Path:
    tdir = tmp_path / "templates"
    _write_templates(tdir)
    return tdir


# ---------------------------------------------------------------------------
# 1. Full generation
# ---------------------------------------------------------------------------


def test_full_generation_writes_all_outputs_and_matches_counts(site, templates):
    counts = generate_assistant_bundle(site, template_dir=templates)

    assert counts == {
        "entries": 3,
        "depends": 1,
        "mentions": 1,
        "files_written": 8,
    }

    assistant = site / "assistant"
    expected = [
        assistant / "skill" / "icones-audit" / "SKILL.md",
        assistant / "skill" / "icones-audit" / "references" / "entries.md",
        assistant / "skill" / "icones-audit" / "references" / "dependencies.md",
        assistant / "skill" / "icones-audit" / "references" / "verification.md",
        assistant / "icones-audit-skill.zip",
        assistant / "chatdata.json",
        assistant / "chatbot.html",
        assistant / "index.html",
    ]
    for path in expected:
        assert path.is_file(), path


# ---------------------------------------------------------------------------
# 2. Drift guard
# ---------------------------------------------------------------------------


def test_no_leftover_placeholder_in_generated_files_with_good_templates(site, templates):
    generate_assistant_bundle(site, template_dir=templates)
    assistant = site / "assistant"
    text_files = [
        assistant / "skill" / "icones-audit" / "SKILL.md",
        assistant / "skill" / "icones-audit" / "references" / "entries.md",
        assistant / "skill" / "icones-audit" / "references" / "dependencies.md",
        assistant / "skill" / "icones-audit" / "references" / "verification.md",
        assistant / "chatdata.json",
        assistant / "chatbot.html",
        assistant / "index.html",
    ]
    for path in text_files:
        text = path.read_text(encoding="utf-8")
        assert not re.search(r"\{\{[A-Z_]+\}\}", text), path


def test_unknown_placeholder_in_template_raises_value_error_naming_marker(tmp_path, site):
    bad_templates = tmp_path / "bad_templates"
    _write_templates(bad_templates, typo=True)
    with pytest.raises(ValueError, match=r"TYPO_KEY"):
        generate_assistant_bundle(site, template_dir=bad_templates)


# ---------------------------------------------------------------------------
# 3. chatdata.json shape
# ---------------------------------------------------------------------------


def test_chatdata_json_round_trips_and_matches_schema(site, templates):
    generate_assistant_bundle(site, template_dir=templates)
    chatdata = json.loads((site / "assistant" / "chatdata.json").read_text(encoding="utf-8"))

    assert chatdata["meta"]["commit"] == COMMIT[:12]
    assert len(chatdata["meta"]["commit"]) == 12
    assert chatdata["meta"]["n_entries"] == 3
    assert chatdata["meta"]["n_depends"] == 1
    assert chatdata["meta"]["n_mentions"] == 1
    assert chatdata["meta"]["tabs"] == {"paper": 2, "ppl": 1, "examples": 0}

    by_id = {e["id"]: e for e in chatdata["entries"]}
    entry = by_id["paper::lem-7-16"]
    for key in (
        "id", "tab", "eid", "label", "kind", "section", "url",
        "status", "leaf", "idents", "files", "text",
    ):
        assert key in entry
    assert entry["tab"] == "paper"
    assert entry["eid"] == "lem-7-16"
    assert entry["leaf"] is False
    assert "x & y" in entry["text"]
    assert "<em>" not in entry["text"]

    assert ["paper::lem-7-16", "paper::def-7-15"] in chatdata["depends"]
    assert ["paper::lem-7-16", "ppl::thm-surface-1"] in chatdata["mentions"]

    assert chatdata["gaps"][0]["label"] == "§ 9"
    assert "Fubini for mixed measures." in chatdata["gaps"][0]["text"]
    assert "Out of scope & deferred." in chatdata["gaps"][0]["why"]


# ---------------------------------------------------------------------------
# 4. chatbot.html marker substitution
# ---------------------------------------------------------------------------


def test_chatbot_html_replaces_data_and_rules_markers(site, templates):
    generate_assistant_bundle(site, template_dir=templates)
    html = (site / "assistant" / "chatbot.html").read_text(encoding="utf-8")

    assert "__CHATDATA_JSON__" not in html
    assert "__CHAT_RULES_JSON__" not in html
    assert f"Built at commit {COMMIT[:12]}" in html

    data_start = html.index("const DATA = ") + len("const DATA = ")
    data_end = html.index(";\n", data_start)
    chatdata = json.loads(html[data_start:data_end])
    assert chatdata["meta"]["n_entries"] == 3

    rules_start = html.index("const RULES = ") + len("const RULES = ")
    rules_end = html.index(";\n", rules_start)
    rules = json.loads(html[rules_start:rules_end])
    expected_chat_header = f"# Chat rules\nCommit {COMMIT[:12]} at https://llm4rocq.github.io/icones-rocq/auditor/\n"
    assert rules.startswith(expected_chat_header)
    assert "## Core guide" in rules


# ---------------------------------------------------------------------------
# 5. Skill zip layout
# ---------------------------------------------------------------------------


def test_skill_zip_has_icones_audit_prefix_and_all_reference_files(site, templates):
    generate_assistant_bundle(site, template_dir=templates)
    zip_path = site / "assistant" / "icones-audit-skill.zip"
    with zipfile.ZipFile(zip_path) as zf:
        names = zf.namelist()

    assert names, "zip is empty"
    assert all(n.startswith("icones-audit/") for n in names)
    assert "icones-audit/SKILL.md" in names
    assert "icones-audit/references/entries.md" in names
    assert "icones-audit/references/dependencies.md" in names
    assert "icones-audit/references/verification.md" in names


# ---------------------------------------------------------------------------
# 6. entries.md content
# ---------------------------------------------------------------------------


def test_entries_md_has_labels_urls_and_leaf_marker_and_truncation(site, templates):
    generate_assistant_bundle(site, template_dir=templates)
    text = (
        site / "assistant" / "skill" / "icones-audit" / "references" / "entries.md"
    ).read_text(encoding="utf-8")

    assert (
        "**Lem 7.16** (`lem-7-16`, kind Lem)" in text
    )
    assert "`is_n_increasing_Delta`" in text
    assert (
        "https://llm4rocq.github.io/icones-rocq/auditor/paper/entries/lem-7-16.html"
        in text
    )

    # The leaf entry (Def 7.15) ends its status segment with "— leaf".
    leaf_lines = [
        line for line in text.splitlines() if line.startswith("- **Def 7.15**")
    ]
    assert len(leaf_lines) == 1
    assert "status: axiom-free, beyond-paper — leaf" in leaf_lines[0]

    # The long statement (Def 7.15) is truncated to 600 chars + ellipsis.
    stmt_lines = [
        line for line in text.splitlines() if line.strip().startswith("Statement:")
    ]
    long_stmt = [l for l in stmt_lines if l.strip().startswith("Statement: word")]
    assert len(long_stmt) == 1
    body = long_stmt[0].split("Statement: ", 1)[1]
    assert body.endswith("…")
    assert len(body) == 601  # 600 chars + the ellipsis character


# ---------------------------------------------------------------------------
# 7. dependencies.md content
# ---------------------------------------------------------------------------


def test_dependencies_md_lists_resolved_depends_and_mentions(site, templates):
    generate_assistant_bundle(site, template_dir=templates)
    text = (
        site / "assistant" / "skill" / "icones-audit" / "references" / "dependencies.md"
    ).read_text(encoding="utf-8")

    assert "Lem 7.16 [paper] → Def 7.15 [paper]" in text
    assert "Lem 7.16 [paper] ↔ Thm S.1 [ppl]" in text


# ---------------------------------------------------------------------------
# 8. Missing inputs
# ---------------------------------------------------------------------------


def test_missing_graph_json_raises_file_not_found_naming_it(tmp_path, templates):
    site_dir = tmp_path / "no_graph_site"
    site_dir.mkdir()
    _write_data_json(site_dir)
    with pytest.raises(FileNotFoundError, match="graph.json"):
        generate_assistant_bundle(site_dir, template_dir=templates)


def test_missing_template_raises_file_not_found_naming_it(site, tmp_path):
    incomplete = tmp_path / "incomplete_templates"
    _write_templates(incomplete)
    (incomplete / "chatbot.html.in").unlink()
    with pytest.raises(FileNotFoundError, match="chatbot.html.in"):
        generate_assistant_bundle(site, template_dir=incomplete)
