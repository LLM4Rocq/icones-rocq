"""Generate the audit-assistant bundle from the site's own published data.

The auditor site (:mod:`tools.build_auditor` / :mod:`tools.auditor.render`)
already publishes two machine-readable artifacts at the root of every build:
``graph.json`` (the dependency graph — see :mod:`tools.auditor.graph`) and
``data.json`` (the full three-tab document, ``schema.three_tab_to_dict``).
This module reads ONLY those two files plus a handful of text templates and
derives an "audit assistant bundle" under ``<site>/assistant/``:

* an Agent Skill (``skill/icones-audit/``, zipped as
  ``icones-audit-skill.zip``) an LLM can load to answer questions about the
  formalisation without re-deriving the graph or re-parsing the markdown;
* a self-contained chat widget (``chatbot.html`` + ``chatdata.json``) that
  embeds the same generated guidance and a compact copy of the graph/entry
  data, for a reader who wants to ask questions right there on the site;
* a landing page (``index.html``) linking both.

Deriving the bundle from ``graph.json``/``data.json`` rather than from the
markdown sources (or worse, hand-maintained separately) keeps ONE source of
truth: whatever the site says is the graph/entries is exactly what the
assistant is told. Nothing here re-parses ``docs/*.md``, walks
``theories/**/*.v``, or touches ``.glob`` files — by the time this module
runs, all of that work is already baked into the two JSON artifacts.

Everything is generated from stdlib only: :mod:`json` for the artifacts,
:mod:`html.parser` for turning ``*_html`` fields into plain prose, and
:mod:`zipfile` for the packaged Skill.

Placeholder substitution
-------------------------
Templates are plain text with ``{{UPPER_SNAKE}}`` placeholders (see
:func:`_substitute`). A small, fixed mapping (:data:`_MAPPING_KEYS`,
assembled once per build in :func:`generate_assistant_bundle`) is offered to
every template. After substituting any file this module writes, a drift
guard (:func:`_check_no_leftover`) re-scans the result for a placeholder
that was never resolved — a typo'd ``{{KEY}}`` in a template fails the build
loudly instead of shipping literally into a generated page.
"""

from __future__ import annotations

import json
import re
import zipfile
from collections import Counter
from html.parser import HTMLParser
from pathlib import Path
from typing import Any

__all__ = ["generate_assistant_bundle"]

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

#: Template files expected in ``template_dir``, each substituted with the
#: same placeholder mapping before use.
_TEMPLATE_FILES: tuple[str, ...] = (
    "core_guide.md.in",
    "skill_header.md.in",
    "chat_header.md.in",
    "landing.html.in",
    "chatbot.html.in",
)

#: Display title per tab slug, shared by every generated reference doc.
_TAB_TITLES: dict[str, str] = {"paper": "Paper", "ppl": "PPL", "examples": "Examples"}

_STATEMENT_TRUNCATE = 600

_PLACEHOLDER_RE = re.compile(r"\{\{([A-Z_]+)\}\}")
_LEFTOVER_RE = re.compile(r"\{\{[A-Z_]+\}\}")


# ---------------------------------------------------------------------------
# Small generic helpers
# ---------------------------------------------------------------------------


def _substitute(text: str, mapping: dict[str, str]) -> str:
    """Replace every ``{{KEY}}`` occurrence with ``mapping["KEY"]``.

    A key absent from ``mapping`` is left untouched — the drift guard
    (:func:`_check_no_leftover`) is what turns that into a build failure,
    with the leftover marker in hand to name in the error.
    """

    def _repl(m: re.Match[str]) -> str:
        key = m.group(1)
        return str(mapping[key]) if key in mapping else m.group(0)

    return _PLACEHOLDER_RE.sub(_repl, text)


def _check_no_leftover(text: str, filename: str) -> None:
    """Raise ``ValueError`` naming ``filename`` and the marker, if any remains."""
    m = _LEFTOVER_RE.search(text)
    if m:
        raise ValueError(
            f"unresolved placeholder {m.group(0)!r} left in generated file "
            f"{filename!r} — a template referenced a key the substitution "
            "mapping does not provide"
        )


def _truncate(text: str, limit: int = _STATEMENT_TRUNCATE) -> str:
    if len(text) > limit:
        return text[:limit] + "…"
    return text


class _TextExtractor(HTMLParser):
    """Collect character data, dropping ``<script>``/``<style>`` content."""

    _SKIPPED_TAGS = ("script", "style")

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self._parts: list[str] = []
        self._skip_depth = 0

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag in self._SKIPPED_TAGS:
            self._skip_depth += 1

    def handle_startendtag(
        self, tag: str, attrs: list[tuple[str, str | None]]
    ) -> None:
        # Self-closed tags never wrap data; nothing to skip.
        pass

    def handle_endtag(self, tag: str) -> None:
        if tag in self._SKIPPED_TAGS and self._skip_depth > 0:
            self._skip_depth -= 1

    def handle_data(self, data: str) -> None:
        if self._skip_depth == 0:
            self._parts.append(data)


def _html_to_text(html: str) -> str:
    """Plain text of an HTML fragment: entities unescaped, tags stripped.

    ``<script>``/``<style>`` content is dropped; all whitespace runs
    (including newlines introduced by block tags) collapse to a single
    space; the result is stripped.
    """
    if not html:
        return ""
    parser = _TextExtractor()
    parser.feed(html)
    parser.close()
    return re.sub(r"\s+", " ", "".join(parser._parts)).strip()


def _read_json(path: Path, label: str) -> Any:
    if not path.is_file():
        raise FileNotFoundError(f"{label} not found: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_template(template_dir: Path, name: str) -> str:
    path = template_dir / name
    if not path.is_file():
        raise FileNotFoundError(f"assistant bundle template not found: {path}")
    return path.read_text(encoding="utf-8")


# ---------------------------------------------------------------------------
# data.json walking
# ---------------------------------------------------------------------------


def _walk_entry_dicts(doc: dict[str, Any]) -> list[dict[str, Any]]:
    """Every entry dict in a tab's ``Document``, sections + chapters + beyond.

    On PPL/Examples, ``beyond`` aliases the chapter-tree entries already
    walked above (see :mod:`tools.auditor.graph`'s ``_collect_nodes``
    docstring) — harmless here since we only build an id-keyed map.
    """
    out: list[dict[str, Any]] = []
    for section in doc.get("sections", []) or []:
        out.extend(section.get("entries", []) or [])
    for chapter in doc.get("chapters", []) or []:
        for section in chapter.get("sections", []) or []:
            out.extend(section.get("entries", []) or [])
    for contrib in doc.get("beyond", []) or []:
        out.extend(contrib.get("entries", []) or [])
    return out


def _build_statement_map(data: dict[str, Any]) -> dict[tuple[str, str], str]:
    """``(tab, entry_id) -> statement_html``, walked once from ``data.json``."""
    out: dict[tuple[str, str], str] = {}
    for tab in _TAB_TITLES:
        doc = data.get(tab, {}) or {}
        for entry in _walk_entry_dicts(doc):
            out[(tab, entry.get("id", ""))] = entry.get("statement_html", "")
    return out


# ---------------------------------------------------------------------------
# graph.json walking
# ---------------------------------------------------------------------------


def _entry_nodes(graph: dict[str, Any]) -> list[dict[str, Any]]:
    """Entry-node ``data`` dicts, in ``graph.json`` node order."""
    return [
        n["data"]
        for n in graph.get("nodes", [])
        if n.get("data", {}).get("ntype") == "entry"
    ]


def _bare_id(node_id: str) -> str:
    """The entry id without its ``<tab>::`` prefix."""
    return node_id.split("::", 1)[-1]


# ---------------------------------------------------------------------------
# entries.md
# ---------------------------------------------------------------------------


def _entry_record_lines(
    node: dict[str, Any], site: str, statement_html: str
) -> list[str]:
    eid = _bare_id(node.get("id", ""))
    idents = ", ".join(f"`{i}`" for i in node.get("idents") or [])
    files = ", ".join(node.get("files") or [])
    statuses = ", ".join(node.get("status") or [])
    status_seg = f"status: {statuses}"
    if node.get("leaf"):
        status_seg += " — leaf"
    url = site + node.get("url", "")
    lines = [
        f"- **{node.get('label', '')}** (`{eid}`, kind {node.get('kind', '')}) "
        f"— {status_seg} — idents: {idents} — files: {files} "
        f"— {url}"
    ]
    text = _html_to_text(statement_html) if statement_html else ""
    if text:
        lines.append(f"  Statement: {_truncate(text)}")
    return lines


def _build_entries_md(
    entry_nodes: list[dict[str, Any]],
    statement_map: dict[tuple[str, str], str],
    mapping: dict[str, str],
    site: str,
) -> str:
    lines = [
        f"# Entry index ({mapping['N_ENTRIES']} entries, commit {mapping['COMMIT']})",
        "",
    ]
    by_tab: dict[str, list[dict[str, Any]]] = {t: [] for t in _TAB_TITLES}
    for d in entry_nodes:
        by_tab.setdefault(d.get("tab", ""), []).append(d)

    for tab, title in _TAB_TITLES.items():
        lines.append(f"## {title}")
        lines.append("")
        # Group by ``group_label``, first-seen order (graph.json node order).
        order: list[str] = []
        buckets: dict[str, list[dict[str, Any]]] = {}
        for d in by_tab.get(tab, []):
            label = d.get("group_label", "")
            if label not in buckets:
                buckets[label] = []
                order.append(label)
            buckets[label].append(d)
        for label in order:
            lines.append(f"### {label}")
            lines.append("")
            for d in buckets[label]:
                statement_html = statement_map.get((tab, _bare_id(d.get("id", ""))), "")
                lines.extend(_entry_record_lines(d, site, statement_html))
            lines.append("")
    return "\n".join(lines).rstrip() + "\n"


# ---------------------------------------------------------------------------
# dependencies.md
# ---------------------------------------------------------------------------


def _append_edge_section(
    lines: list[str],
    edges: list[dict[str, Any]],
    entry_by_id: dict[str, dict[str, Any]],
    arrow: str,
) -> None:
    order: list[str] = []
    groups: dict[str, list[str]] = {}
    for e in edges:
        src, tgt = e.get("source", ""), e.get("target", "")
        s_node, t_node = entry_by_id.get(src), entry_by_id.get(tgt)
        if s_node is None or t_node is None:
            continue
        src_tab = s_node.get("tab", "")
        line = (
            f"- {s_node.get('label', '')} [{s_node.get('tab', '')}] {arrow} "
            f"{t_node.get('label', '')} [{t_node.get('tab', '')}]"
        )
        if src_tab not in groups:
            groups[src_tab] = []
            order.append(src_tab)
        groups[src_tab].append(line)
    for tab in order:
        lines.append(f"### {_TAB_TITLES.get(tab, tab)}")
        lines.append("")
        lines.extend(groups[tab])
        lines.append("")


def _build_dependencies_md(
    graph: dict[str, Any], mapping: dict[str, str]
) -> str:
    entry_by_id = {d.get("id", ""): d for d in _entry_nodes(graph)}
    edges = [e["data"] for e in graph.get("edges", [])]
    depends = [e for e in edges if e.get("kind") == "depends"]
    mentions = [e for e in edges if e.get("kind") == "mentions"]

    lines = [
        "# Dependencies",
        "",
        "Statement-level dependency edges read from the Rocq .glob files; "
        "references made only inside proof scripts are excluded.",
        "",
        f"{mapping['N_DEPENDS']} depends edges · {mapping['N_MENTIONS']} "
        f"mentions edges · {mapping['N_LEAVES']} leaves",
        "",
        "## Depends (A → B: A's statement uses B)",
        "",
    ]
    _append_edge_section(lines, depends, entry_by_id, "→")
    lines.append("## Mentions (undirected co-reference)")
    lines.append("")
    _append_edge_section(lines, mentions, entry_by_id, "↔")
    return "\n".join(lines).rstrip() + "\n"


# ---------------------------------------------------------------------------
# verification.md
# ---------------------------------------------------------------------------


def _build_verification_md(data: dict[str, Any]) -> str:
    lines = ["# How to verify", ""]
    for tab, title in _TAB_TITLES.items():
        html = (data.get(tab, {}) or {}).get("verify_instructions_html", "")
        if not html:
            continue
        lines.append(f"## {title}")
        lines.append("")
        lines.append(_html_to_text(html))
        lines.append("")

    lines.append("## Axiom anchors")
    lines.append("")
    axiom_anchors = (data.get("paper", {}) or {}).get("axiom_anchors") or {}
    regression = axiom_anchors.get("regression", "")
    if regression:
        lines.append(f"- {regression}")
    for headline in axiom_anchors.get("headlines", []) or []:
        lines.append(f"- {headline}")
    lines.append("")

    lines.append("## Documented gaps")
    lines.append("")
    for gap in (data.get("paper", {}) or {}).get("gaps", []) or []:
        desc = _html_to_text(gap.get("description_html", ""))
        reason = _html_to_text(gap.get("reason_html", ""))
        lines.append(f"- **{gap.get('paper_label', '')}** — {desc} (why: {reason})")

    return "\n".join(lines).rstrip() + "\n"


# ---------------------------------------------------------------------------
# chatdata.json
# ---------------------------------------------------------------------------


def _build_chatdata(
    graph: dict[str, Any],
    data: dict[str, Any],
    statement_map: dict[tuple[str, str], str],
    mapping: dict[str, str],
    commit: str,
    site: str,
) -> dict[str, Any]:
    entry_nodes = _entry_nodes(graph)
    status_counts: Counter[str] = Counter()
    tab_counts: Counter[str] = Counter()
    entries: list[dict[str, Any]] = []
    for d in entry_nodes:
        tab = d.get("tab", "")
        for st in d.get("status") or []:
            status_counts[st] += 1
        tab_counts[tab] += 1
        eid = _bare_id(d.get("id", ""))
        statement_html = statement_map.get((tab, eid), "")
        text = _truncate(_html_to_text(statement_html)) if statement_html else ""
        entries.append(
            {
                "id": d.get("id", ""),
                "tab": tab,
                "eid": eid,
                "label": d.get("label", ""),
                "kind": d.get("kind", ""),
                "section": d.get("group_label", ""),
                "url": d.get("url", ""),
                "status": list(d.get("status") or []),
                "leaf": bool(d.get("leaf", False)),
                "idents": list(d.get("idents") or []),
                "files": list(d.get("files") or []),
                "text": text,
            }
        )

    edges = [e["data"] for e in graph.get("edges", [])]
    depends = [
        [e["source"], e["target"]] for e in edges if e.get("kind") == "depends"
    ]
    mentions = [
        [e["source"], e["target"]] for e in edges if e.get("kind") == "mentions"
    ]

    gaps = [
        {
            "label": g.get("paper_label", ""),
            "text": _html_to_text(g.get("description_html", "")),
            "why": _html_to_text(g.get("reason_html", "")),
        }
        for g in (data.get("paper", {}) or {}).get("gaps", []) or []
    ]

    return {
        "meta": {
            "commit": commit,
            "built_at": mapping["BUILT_AT"],
            "site": site,
            "n_entries": int(mapping["N_ENTRIES"]),
            "n_depends": int(mapping["N_DEPENDS"]),
            "n_mentions": int(mapping["N_MENTIONS"]),
            "status_counts": dict(status_counts),
            "tabs": {t: tab_counts.get(t, 0) for t in _TAB_TITLES},
        },
        "entries": entries,
        "depends": depends,
        "mentions": mentions,
        "gaps": gaps,
    }


# ---------------------------------------------------------------------------
# The Skill zip
# ---------------------------------------------------------------------------


def _build_zip(skill_root: Path, zip_path: Path) -> None:
    """Zip ``skill_root`` (which already contains an ``icones-audit/`` dir).

    Archive member paths are ``skill_root``-relative, so they start with
    ``icones-audit/`` — the layout an Agent Skill loader expects to unpack.
    """
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
        for path in sorted(skill_root.rglob("*")):
            if path.is_file():
                zf.write(path, path.relative_to(skill_root).as_posix())


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def generate_assistant_bundle(
    site_dir: str | Path,
    *,
    site_url: str = "https://llm4rocq.github.io/icones-rocq/auditor/",
    template_dir: str | Path | None = None,
    artifact_url: str = "",
) -> dict[str, int]:
    """Build ``<site_dir>/assistant/`` from that site's own ``graph.json``
    / ``data.json``, plus the text templates in ``template_dir``.

    ``template_dir`` defaults to the bundled ``tools/auditor/assistant/``
    directory next to this module; pass an explicit one (as the tests do)
    to point at stand-in templates instead.

    ``artifact_url``, when non-empty, is substituted as ``{{ARTIFACT_URL}}``
    (e.g. a published claude.ai artifact hosting a richer chat experience);
    left as an empty string otherwise — templates are written to cope with
    that.

    Returns a small counts dict (``entries``, ``depends``, ``mentions``,
    ``files_written``) for the build log.
    """
    site = Path(site_dir)
    graph = _read_json(site / "graph.json", "graph.json")
    data = _read_json(site / "data.json", "data.json")

    tdir = (
        Path(template_dir)
        if template_dir is not None
        else Path(__file__).parent / "assistant"
    )
    templates = {name: _read_template(tdir, name) for name in _TEMPLATE_FILES}

    graph_meta = graph.get("meta", {}) or {}
    edges = [e["data"] for e in graph.get("edges", [])]
    entry_nodes = _entry_nodes(graph)

    n_entries = graph_meta.get("n_entries", len(entry_nodes))
    n_depends = graph_meta.get(
        "n_depends", sum(1 for e in edges if e.get("kind") == "depends")
    )
    n_mentions = graph_meta.get(
        "n_mentions", sum(1 for e in edges if e.get("kind") == "mentions")
    )
    n_leaves = graph_meta.get(
        "n_leaves", sum(1 for d in entry_nodes if d.get("leaf"))
    )

    build_meta = data.get("build_meta", {}) or {}
    commit = str(build_meta.get("commit", ""))[:12]
    built_at = build_meta.get("built_at", "")

    site_norm = site_url if site_url.endswith("/") else site_url + "/"

    status_counter: Counter[str] = Counter()
    tab_counter: Counter[str] = Counter()
    for d in entry_nodes:
        for st in d.get("status") or []:
            status_counter[st] += 1
        tab_counter[d.get("tab", "")] += 1
    status_rows = sorted(status_counter.items(), key=lambda kv: (-kv[1], kv[0]))
    status_counts_md = "\n".join(f"| {s} | {c} |" for s, c in status_rows)
    tab_counts_line = (
        f"Paper: {tab_counter.get('paper', 0)} entries · "
        f"PPL: {tab_counter.get('ppl', 0)} · "
        f"Examples: {tab_counter.get('examples', 0)}"
    )

    mapping: dict[str, str] = {
        "N_ENTRIES": str(n_entries),
        "N_DEPENDS": str(n_depends),
        "N_MENTIONS": str(n_mentions),
        "N_LEAVES": str(n_leaves),
        "COMMIT": commit,
        "BUILT_AT": built_at,
        "SITE": site_norm,
        "ARTIFACT_URL": artifact_url,
        "SKILL_ZIP_URL": f"{site_norm}assistant/icones-audit-skill.zip",
        "STATUS_COUNTS": status_counts_md,
        "TAB_COUNTS": tab_counts_line,
    }

    assistant_dir = site / "assistant"
    skill_dir = assistant_dir / "skill" / "icones-audit"
    refs_dir = skill_dir / "references"

    files_written = 0

    def _emit(path: Path, text: str) -> None:
        nonlocal files_written
        _check_no_leftover(text, str(path))
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        files_written += 1

    # 1. SKILL.md = skill_header + core_guide.
    skill_header = _substitute(templates["skill_header.md.in"], mapping)
    core_guide = _substitute(templates["core_guide.md.in"], mapping)
    _emit(skill_dir / "SKILL.md", skill_header + "\n" + core_guide)

    statement_map = _build_statement_map(data)

    # 2-4. Generated reference docs.
    _emit(
        refs_dir / "entries.md",
        _build_entries_md(entry_nodes, statement_map, mapping, site_norm),
    )
    _emit(refs_dir / "dependencies.md", _build_dependencies_md(graph, mapping))
    _emit(refs_dir / "verification.md", _build_verification_md(data))

    # 5. The packaged Skill zip (built last, once every skill/ file exists).
    zip_path = assistant_dir / "icones-audit-skill.zip"
    _build_zip(assistant_dir / "skill", zip_path)
    files_written += 1

    # 6. chatdata.json.
    chatdata = _build_chatdata(graph, data, statement_map, mapping, commit, site_norm)
    chatdata_text = json.dumps(chatdata, separators=(",", ":"), ensure_ascii=False)
    _check_no_leftover(chatdata_text, "chatdata.json")
    (assistant_dir / "chatdata.json").write_text(chatdata_text, encoding="utf-8")
    files_written += 1

    # 7. chatbot.html: {{...}} placeholders, then the two __MARKER__ swaps.
    chat_header = _substitute(templates["chat_header.md.in"], mapping)
    rules_text = chat_header + "\n" + core_guide
    chatbot_html = _substitute(templates["chatbot.html.in"], mapping)
    chatbot_html = chatbot_html.replace("__CHATDATA_JSON__", chatdata_text)
    chatbot_html = chatbot_html.replace(
        "__CHAT_RULES_JSON__", json.dumps(rules_text, ensure_ascii=False)
    )
    _emit(assistant_dir / "chatbot.html", chatbot_html)

    # 8. index.html landing page.
    _emit(assistant_dir / "index.html", _substitute(templates["landing.html.in"], mapping))

    return {
        "entries": n_entries,
        "depends": n_depends,
        "mentions": n_mentions,
        "files_written": files_written,
    }
