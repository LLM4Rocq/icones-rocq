"""Jinja2 driver that emits the static-site artefacts under ``site/auditor/``.

Layout (file URLs, matching the UI templates' ``xref_href`` convention):

    out/index.html                  root landing (triple-tab summary)
    out/data.json                   combined Paper + PPL + Examples JSON export
    out/static/{style,print,pygments}.css, app.js
    out/paper/index.html            Paper-tab landing
    out/paper/sections/<id>.html
    out/paper/entries/<id>.html
    out/paper/beyond/<id>.html
    out/paper/gaps.html
    out/paper/data.json             Paper-only JSON export
    out/ppl/...                     mirror of the above for the PPL tab
    out/examples/...                mirror of the above for the Examples tab

Per-template context contracts:

``root.html``     : ``{paper, ppl, examples, build_meta, tab=None}``
``index.html``    : ``{document, sections, beyond, gaps, axiom_anchors, build_meta, tab}``
``section.html``  : ``{document, section, entries, build_meta, tab}``
``entry.html``    : ``{document, entry, section, contrib?, build_meta, tab}``
``beyond.html``   : ``{document, contrib, entries, build_meta, tab}``
``gap.html``      : ``{document, gaps, build_meta, tab}``

Each render registers Jinja globals ``root_prefix``, ``static_prefix``,
``tab_prefix``, ``xref_href`` and an ``is contains`` test, so the UI
templates' macros resolve correctly regardless of nesting depth.
"""

from __future__ import annotations

import json
import shutil
from dataclasses import asdict
from pathlib import Path
from typing import Any

from jinja2 import ChoiceLoader, Environment, FileSystemLoader, TemplateNotFound, select_autoescape
from pygments.formatters import HtmlFormatter

from .schema import (
    TAB_EXAMPLES,
    TAB_PAPER,
    TAB_PPL,
    Document,
    ThreeTabDocument,
    three_tab_to_dict,
)


BUNDLED_TEMPLATE_DIR = Path(__file__).parent / "templates"
BUNDLED_STATIC_DIR = Path(__file__).parent / "static"
PLACEHOLDER_NAME = "__placeholder.html"


def _xref_href(prefix: str):
    """Build a `cross_refs` URL resolver bound to the given URL prefix.

    The prefix already points at the current tab's root (e.g. ``"../"`` from
    a Paper section page back to ``out/paper/``); the resolver appends the
    sub-route. ``blueprint`` cross-refs go up one more level to ``out/``.
    """
    def _h(xref: Any) -> str:
        # xref may be a dataclass or a dict; tolerate both.
        kind = getattr(xref, "kind", None) or xref.get("kind", "")
        tgt = getattr(xref, "target", None) or xref.get("target", "")
        if kind == "section":
            return f"{prefix}sections/{tgt}.html"
        if kind == "entry":
            return f"{prefix}entries/{tgt}.html"
        if kind == "beyond":
            return f"{prefix}beyond/{tgt}.html"
        if kind == "chapter":
            return f"{prefix}chapters/{tgt}.html"
        if kind == "blueprint":
            return f"{prefix}../../blueprint/{tgt}"
        return "#" + tgt
    return _h


def _depth_prefix(rel_path: Path) -> str:
    """Relative path back to the page's containing tree-root from ``rel_path``.

    Examples (rel_path / returned prefix):
        Path("index.html")                          -> ""
        Path("paper/index.html")                    -> ""        (depth 1 within paper/)
        Path("paper/sections/foo.html")             -> "../"     (climb out of sections/)

    The caller chooses the tree-root: the root landing uses the full path
    depth, while per-tab pages compute their depth relative to the tab
    subtree (so the tab landing's prefix is ``""``).
    """
    depth = len(rel_path.parts) - 1
    return "../" * depth if depth else ""


def _make_env(template_dir: Path | None) -> Environment:
    """Build the Jinja2 environment with two stacked loaders."""
    loaders = []
    if template_dir is not None:
        loaders.append(FileSystemLoader(str(template_dir)))
    loaders.append(FileSystemLoader(str(BUNDLED_TEMPLATE_DIR)))
    env = Environment(
        loader=ChoiceLoader(loaders),
        autoescape=select_autoescape(enabled_extensions=("html", "htm")),
        keep_trailing_newline=True,
        trim_blocks=True,
        lstrip_blocks=True,
    )
    # UI templates use `selectattr('status', 'contains', 'axiom-free')` —
    # vanilla Jinja2 has no `contains` test; register one (membership test
    # on the attribute value, which is a list/string).
    env.tests["contains"] = lambda lst, item: item in (lst or [])
    return env


def _render_template(env: Environment, name: str, ctx: dict[str, Any]) -> str:
    """Render a named template; fall back to the placeholder if missing."""
    try:
        tmpl = env.get_template(name)
    except TemplateNotFound:
        tmpl = env.get_template(PLACEHOLDER_NAME)
        ctx.setdefault("title", name.replace(".html", "").title())
        ctx.setdefault("body", "<p><em>Template not yet implemented.</em></p>")
    return tmpl.render(**ctx)


def _emit(
    env: Environment,
    out: Path,
    rel: Path,
    template: str,
    ctx: dict[str, Any],
    *,
    root_prefix: str,
    static_prefix: str,
    tab_prefix: str,
) -> None:
    """Render `template` with depth-aware globals and write to ``out/rel``.

    - ``root_prefix`` resolves URLs *within the current tab* (or, for the
      root landing, within the whole site).
    - ``static_prefix`` resolves to ``out/static/`` from the page location.
    - ``tab_prefix`` resolves to ``out/`` (i.e. the site root) — used by
      the tab nav to link between Paper and PPL tabs.
    """
    env.globals["root_prefix"] = root_prefix
    env.globals["static_prefix"] = static_prefix
    env.globals["tab_prefix"] = tab_prefix
    env.globals["xref_href"] = _xref_href(root_prefix)
    ctx = {
        **ctx,
        "root_prefix": root_prefix,
        "static_prefix": static_prefix,
        "tab_prefix": tab_prefix,
        "xref_href": _xref_href(root_prefix),
    }
    dest = out / rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(_render_template(env, template, ctx), encoding="utf-8")


def _emit_tab(
    env: Environment,
    out: Path,
    tab: str,
    doc: Document,
    build_meta: Any,
) -> dict[str, int]:
    """Emit one tab's subtree under ``out/<tab>/``.

    Returns the per-tab artefact counts. The build_meta passed in
    overrides the doc's own metadata for footer rendering (the dashboard
    publishes a single set of provenance values).
    """
    counts = {
        "index": 0, "sections": 0, "entries": 0, "beyond": 0,
        "gaps": 0, "json": 0, "chapters": 0,
    }
    tab_dir = Path(tab)

    # Inject the shared build_meta so templates pick it up via doc.build_meta.
    doc.build_meta = build_meta

    # Per-tab data.json export.
    (out / tab_dir / "data.json").parent.mkdir(parents=True, exist_ok=True)
    (out / tab_dir / "data.json").write_text(
        json.dumps(asdict(doc), indent=2), encoding="utf-8"
    )
    counts["json"] = 1

    def _prefixes(rel_within_tab: Path) -> tuple[str, str, str]:
        # Prefix back to the tab's root.
        root_p = _depth_prefix(rel_within_tab)
        # Static lives at out/static/ — two levels up from a depth-1 page.
        # rel_within_tab depth = N, plus 1 for the tab dir itself.
        depth_total = len(rel_within_tab.parts)
        static_p = "../" * depth_total
        # Tab prefix: back to out/.
        tab_p = static_p
        return root_p, static_p, tab_p

    # -- per-tab index --------------------------------------------------
    rel = tab_dir / "index.html"
    root_p, static_p, tab_p = _prefixes(Path("index.html"))
    _emit(
        env, out, rel, "index.html",
        {
            "document": doc,
            "sections": doc.sections,
            "beyond": doc.beyond,
            "gaps": doc.gaps,
            "axiom_anchors": doc.axiom_anchors,
            "build_meta": build_meta,
            "tab": tab,
            "title": f"Auditor — {tab.upper()}",
            "body": _summary_html(doc),
        },
        root_prefix=root_p, static_prefix=static_p, tab_prefix=tab_p,
    )
    counts["index"] = 1

    if doc.chapters:
        # Chapter-tree path (PPL / Examples).  Emit chapter / section /
        # entry pages from ``doc.chapters``; skip the legacy ``beyond/``
        # tree (the chapter tree replaces it).
        for chapter in doc.chapters:
            rel_c = Path("chapters") / f"{chapter.id}.html"
            root_p, static_p, tab_p = _prefixes(rel_c)
            _emit(
                env, out, tab_dir / rel_c, "chapter.html",
                {
                    "document": doc,
                    "chapter": chapter,
                    "build_meta": build_meta,
                    "tab": tab,
                    "title": chapter.title,
                    "body": _chapter_body_html(chapter),
                },
                root_prefix=root_p, static_prefix=static_p, tab_prefix=tab_p,
            )
            counts["chapters"] += 1

            for section in chapter.sections:
                rel_s = Path("sections") / f"{section.id}.html"
                root_p, static_p, tab_p = _prefixes(rel_s)
                _emit(
                    env, out, tab_dir / rel_s, "section.html",
                    {
                        "document": doc,
                        "section": section,
                        "chapter": chapter,
                        "entries": section.entries,
                        "build_meta": build_meta,
                        "tab": tab,
                        "title": section.title or section.id,
                        "body": _section_body_html(section),
                    },
                    root_prefix=root_p, static_prefix=static_p, tab_prefix=tab_p,
                )
                counts["sections"] += 1

                for entry in section.entries:
                    rel_e = Path("entries") / f"{entry.id}.html"
                    root_p, static_p, tab_p = _prefixes(rel_e)
                    _emit(
                        env, out, tab_dir / rel_e, "entry.html",
                        {
                            "document": doc,
                            "entry": entry,
                            "section": section,
                            "chapter": chapter,
                            "build_meta": build_meta,
                            "tab": tab,
                            "title": entry.paper_label,
                            "body": _entry_body_html(entry),
                        },
                        root_prefix=root_p, static_prefix=static_p, tab_prefix=tab_p,
                    )
                    counts["entries"] += 1
    else:
        # Legacy paper-style tree: H2 sections + Beyond contribs.

        # -- per-section + per-entry -----------------------------------
        for section in doc.sections:
            rel_within = Path("sections") / f"{section.id}.html"
            root_p, static_p, tab_p = _prefixes(rel_within)
            _emit(
                env, out, tab_dir / rel_within, "section.html",
                {
                    "document": doc,
                    "section": section,
                    "entries": section.entries,
                    "build_meta": build_meta,
                    "tab": tab,
                    "title": section.title or section.id,
                    "body": _section_body_html(section),
                },
                root_prefix=root_p, static_prefix=static_p, tab_prefix=tab_p,
            )
            counts["sections"] += 1

            for entry in section.entries:
                rel_e = Path("entries") / f"{entry.id}.html"
                root_p, static_p, tab_p = _prefixes(rel_e)
                _emit(
                    env, out, tab_dir / rel_e, "entry.html",
                    {
                        "document": doc,
                        "entry": entry,
                        "section": section,
                        "build_meta": build_meta,
                        "tab": tab,
                        "title": entry.paper_label,
                        "body": _entry_body_html(entry),
                    },
                    root_prefix=root_p, static_prefix=static_p, tab_prefix=tab_p,
                )
                counts["entries"] += 1

        # -- beyond contribs + their entries ---------------------------
        for contrib in doc.beyond:
            rel_b = Path("beyond") / f"{contrib.id}.html"
            root_p, static_p, tab_p = _prefixes(rel_b)
            _emit(
                env, out, tab_dir / rel_b, "beyond.html",
                {
                    "document": doc,
                    "beyond": contrib,         # UI templates name it `beyond`
                    "contrib": contrib,        # legacy alias for the placeholder
                    "entries": contrib.entries,
                    "build_meta": build_meta,
                    "tab": tab,
                    "title": contrib.title,
                    "body": _beyond_body_html(contrib),
                },
                root_prefix=root_p, static_prefix=static_p, tab_prefix=tab_p,
            )
            counts["beyond"] += 1
            for entry in contrib.entries:
                rel_e = Path("entries") / f"{entry.id}.html"
                root_p, static_p, tab_p = _prefixes(rel_e)
                _emit(
                    env, out, tab_dir / rel_e, "entry.html",
                    {
                        "document": doc,
                        "entry": entry,
                        "section": None,
                        "contrib": contrib,
                        "build_meta": build_meta,
                        "tab": tab,
                        "title": entry.paper_label,
                        "body": _entry_body_html(entry),
                    },
                    root_prefix=root_p, static_prefix=static_p, tab_prefix=tab_p,
                )
                counts["entries"] += 1

    # -- single gaps page ----------------------------------------------
    rel_g = Path("gaps.html")
    root_p, static_p, tab_p = _prefixes(rel_g)
    _emit(
        env, out, tab_dir / rel_g, "gap.html",
        {
            "document": doc,
            "gaps": doc.gaps,
            "build_meta": build_meta,
            "tab": tab,
            "title": "Not formalised",
            "body": _gaps_body_html(doc.gaps),
        },
        root_prefix=root_p, static_prefix=static_p, tab_prefix=tab_p,
    )
    counts["gaps"] = len(doc.gaps)

    return counts


def render(
    doc: ThreeTabDocument,
    out_dir: str | Path,
    *,
    template_dir: str | Path | None = None,
) -> dict[str, int]:
    """Emit the triple-tab dashboard under ``out_dir``.

    Returns a counter of artefacts written (``index``, ``sections``,
    ``entries``, ``beyond``, ``gaps``, ``static``, ``json``, ``tabs``).
    The counts aggregate every tab; the root landing and combined
    ``data.json`` are also included.
    """
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)

    env = _make_env(Path(template_dir) if template_dir else None)
    totals = {
        "index": 0, "sections": 0, "entries": 0, "beyond": 0,
        "gaps": 0, "json": 0, "tabs": 0, "chapters": 0,
    }

    # -- static assets (copied from bundled tree, plus generated pygments.css) -
    static_out = out / "static"
    if static_out.exists():
        shutil.rmtree(static_out)
    if BUNDLED_STATIC_DIR.exists():
        shutil.copytree(BUNDLED_STATIC_DIR, static_out)
    else:
        static_out.mkdir(parents=True, exist_ok=True)
    css = HtmlFormatter(cssclass="highlight coq").get_style_defs(".highlight")
    (static_out / "pygments.css").write_text(css, encoding="utf-8")

    # -- combined data.json ---------------------------------------------
    (out / "data.json").write_text(
        json.dumps(three_tab_to_dict(doc), indent=2), encoding="utf-8"
    )
    totals["json"] += 1

    # -- root landing (no tab highlighted) ------------------------------
    # The root landing lives at out/index.html: depth-0 from itself.
    _emit(
        env, out, Path("index.html"), "root.html",
        {
            "document": doc.paper,   # footer macros reach into build_meta etc.
            "paper": doc.paper,
            "ppl": doc.ppl,
            "examples": doc.examples,
            "build_meta": doc.build_meta,
            "tab": None,
            "title": "ICones — Auditor",
            "body": _root_summary_html(doc),
        },
        root_prefix="", static_prefix="", tab_prefix="",
    )

    # -- every tab ------------------------------------------------------
    tab_docs = (
        (TAB_PAPER, doc.paper),
        (TAB_PPL, doc.ppl),
        (TAB_EXAMPLES, doc.examples),
    )
    for tab_name, tab_doc in tab_docs:
        per = _emit_tab(env, out, tab_name, tab_doc, doc.build_meta)
        totals["tabs"] += 1
        for k in ("index", "sections", "entries", "beyond", "gaps", "json", "chapters"):
            totals[k] += per[k]

    return totals


# -- small helpers used by the placeholder template -------------------------


def _status_pills(statuses: list[str]) -> str:
    return "".join(
        f'<span class="status status-{s}">{s}</span>' for s in statuses
    )


def _summary_html(doc: Document) -> str:
    rows = ["<p>Sections:</p><ul>"]
    for s in doc.sections:
        rows.append(
            f'<li><a href="sections/{s.id}.html">{s.paper_section}</a> — '
            f"{len(s.entries)} entries</li>"
        )
    rows.append("</ul>")
    rows.append("<p>Beyond:</p><ul>")
    for b in doc.beyond:
        rows.append(
            f'<li><a href="beyond/{b.id}.html">{b.title}</a> — '
            f"{len(b.entries)} entries</li>"
        )
    rows.append("</ul>")
    if doc.gaps:
        rows.append(f'<p><a href="gaps.html">Gaps ({len(doc.gaps)})</a></p>')
    return "\n".join(rows)


def _root_summary_html(three: ThreeTabDocument) -> str:
    def _tab_block(label: str, slug: str, tab_doc: Document) -> str:
        if tab_doc.chapters:
            # PPL / Examples chapter tree.
            n_sections = sum(len(c.sections) for c in tab_doc.chapters)
            n_entries = sum(
                len(s.entries) for c in tab_doc.chapters for s in c.sections
            )
            summary = (
                f"{len(tab_doc.chapters)} chapters · {n_sections} sections · "
                f"{n_entries} entries · {len(tab_doc.gaps)} gaps."
            )
        else:
            n_entries = sum(len(s.entries) for s in tab_doc.sections) + sum(
                len(b.entries) for b in tab_doc.beyond
            )
            summary = (
                f"{len(tab_doc.sections)} sections · {len(tab_doc.beyond)} beyond · "
                f"{len(tab_doc.gaps)} gaps · {n_entries} entries."
            )
        return (
            f'<section class="tab-card"><h2>{label}</h2>'
            f"<p>{summary}</p>"
            f'<p><a class="cta" href="{slug}/index.html">Open {label} →</a></p>'
            f"</section>"
        )
    parts = ['<div class="root-tabs">']
    parts.append(_tab_block("Paper", "paper", three.paper))
    parts.append(_tab_block("PPL", "ppl", three.ppl))
    parts.append(_tab_block("Examples", "examples", three.examples))
    parts.append("</div>")
    return "\n".join(parts)


def _section_body_html(section: Any) -> str:
    parts = [section.intro_html, "<ul>"]
    for e in section.entries:
        parts.append(
            f'<li><a href="../entries/{e.id}.html"><strong>{e.paper_label}</strong></a> '
            f"{_status_pills(e.status)} — {e.statement_html}</li>"
        )
    parts.append("</ul>")
    if section.notes_html:
        parts.append('<div class="note">' + section.notes_html + "</div>")
    return "\n".join(parts)


def _gaps_body_html(gaps: list[Any]) -> str:
    parts = ["<ul>"]
    for g in gaps:
        parts.append(
            f"<li><strong>{g.paper_label}</strong> — "
            f"{g.description_html}<br><em>{g.reason_html}</em></li>"
        )
    parts.append("</ul>")
    return "\n".join(parts)


def _entry_body_html(entry: Any) -> str:
    parts = [
        f"<h2>{entry.paper_label} {_status_pills(entry.status)}</h2>",
        f"<p>{entry.statement_html}</p>",
    ]
    if entry.rocq_idents:
        parts.append(
            "<p><strong>Identifiers:</strong> "
            + ", ".join(f"<code>{i}</code>" for i in entry.rocq_idents)
            + "</p>"
        )
    if entry.rocq_files:
        parts.append("<p><strong>Files:</strong></p><ul>")
        for f in entry.rocq_files:
            parts.append(
                f'<li><a href="{f.github_url}"><code>{f.path}</code></a>'
                # coqdoc links suppressed: deployment currently absent; re-enable when live.
                + "</li>"
            )
        parts.append("</ul>")
    if entry.detail is not None:
        if entry.detail.prose_html:
            parts.append(entry.detail.prose_html)
        for n in entry.detail.notes:
            parts.append(f'<div class="note">{n.html}</div>')
        for s in entry.detail.snippets:
            parts.append(s.highlighted_html)
    return "\n".join(parts)


def _chapter_body_html(chapter: Any) -> str:
    parts = [chapter.intro_html, "<ul>"]
    for s in chapter.sections:
        parts.append(
            f'<li><a href="../sections/{s.id}.html"><strong>{s.title}</strong></a> — '
            f"{len(s.entries)} entries</li>"
        )
    parts.append("</ul>")
    stats = chapter.stats
    parts.append(
        f"<p class='stats-line'>{stats.n_defs} defs · {stats.n_thms} thms · "
        f"{stats.n_snippets} snippets · {stats.loc} LoC</p>"
    )
    if chapter.notes_html:
        parts.append('<div class="note">' + chapter.notes_html + "</div>")
    return "\n".join(parts)


def _beyond_body_html(contrib: Any) -> str:
    parts = [contrib.intro_html, "<ul>"]
    for e in contrib.entries:
        parts.append(
            f'<li><a href="../entries/{e.id}.html"><strong>{e.paper_label}</strong></a> '
            f"{_status_pills(e.status)} — {e.statement_html}</li>"
        )
    parts.append("</ul>")
    return "\n".join(parts)
