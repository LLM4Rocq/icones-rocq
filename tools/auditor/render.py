"""Jinja2 driver that emits the static-site artefacts under ``site/auditor/``.

Layout (file URLs, matching the UI templates' ``xref_href`` convention):

    out/index.html
    out/sections/<id>.html
    out/entries/<id>.html
    out/beyond/<id>.html
    out/gaps.html              (single page listing all gaps)
    out/static/{style,print,pygments}.css, app.js
    out/data.json              (canonical export)

Per-template context contracts:

``index.html``    : ``{document, sections, beyond, gaps, axiom_anchors, build_meta}``
``section.html``  : ``{document, section, entries, build_meta}``
``entry.html``    : ``{document, entry, section, contrib?, build_meta}``
``beyond.html``   : ``{document, contrib, entries, build_meta}``
``gap.html``      : ``{document, gaps, build_meta}``

Each render registers Jinja globals ``root_prefix``, ``static_prefix``,
``xref_href`` and an ``is contains`` test, so the UI templates' macros
resolve correctly regardless of nesting depth.
"""

from __future__ import annotations

import json
import shutil
from dataclasses import asdict
from pathlib import Path
from typing import Any

from jinja2 import ChoiceLoader, Environment, FileSystemLoader, TemplateNotFound, select_autoescape
from pygments.formatters import HtmlFormatter

from .schema import Document


BUNDLED_TEMPLATE_DIR = Path(__file__).parent / "templates"
BUNDLED_STATIC_DIR = Path(__file__).parent / "static"
PLACEHOLDER_NAME = "__placeholder.html"


def _xref_href(prefix: str):
    """Build a `cross_refs` URL resolver bound to the given root prefix."""
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
        if kind == "blueprint":
            return f"{prefix}../blueprint/{tgt}"
        return "#" + tgt
    return _h


def _depth_prefix(rel_path: Path) -> str:
    """Relative path back to ``out/`` from a file at ``rel_path``."""
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


def _emit(env: Environment, out: Path, rel: Path, template: str,
          ctx: dict[str, Any]) -> None:
    """Render `template` with depth-aware globals and write to ``out/rel``."""
    prefix = _depth_prefix(rel)
    env.globals["root_prefix"] = prefix
    env.globals["static_prefix"] = prefix
    env.globals["xref_href"] = _xref_href(prefix)
    ctx = {
        **ctx,
        "root_prefix": prefix,
        "static_prefix": prefix,
        "xref_href": _xref_href(prefix),
    }
    dest = out / rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(_render_template(env, template, ctx), encoding="utf-8")


def render(
    doc: Document,
    out_dir: str | Path,
    *,
    template_dir: str | Path | None = None,
) -> dict[str, int]:
    """Emit the dashboard under ``out_dir``.

    Returns a counter of artefacts written (``index``, ``sections``,
    ``entries``, ``beyond``, ``gaps``, ``static``, ``json``).
    """
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)

    env = _make_env(Path(template_dir) if template_dir else None)
    counts = {"index": 0, "sections": 0, "entries": 0, "beyond": 0, "gaps": 0, "json": 0}

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

    # -- data.json (canonical export) ------------------------------------
    payload = asdict(doc)
    (out / "data.json").write_text(json.dumps(payload, indent=2), encoding="utf-8")
    counts["json"] = 1

    # -- index -----------------------------------------------------------
    _emit(env, out, Path("index.html"), "index.html", {
        "document": doc,
        "sections": doc.sections,
        "beyond": doc.beyond,
        "gaps": doc.gaps,
        "axiom_anchors": doc.axiom_anchors,
        "build_meta": doc.build_meta,
        "title": "Auditor",
        "body": _summary_html(doc),
    })
    counts["index"] = 1

    # -- per-section + per-entry ----------------------------------------
    for section in doc.sections:
        _emit(env, out, Path("sections") / f"{section.id}.html", "section.html", {
            "document": doc,
            "section": section,
            "entries": section.entries,
            "build_meta": doc.build_meta,
            "title": section.title or section.id,
            "body": _section_body_html(section),
        })
        counts["sections"] += 1

        for entry in section.entries:
            _emit(env, out, Path("entries") / f"{entry.id}.html", "entry.html", {
                "document": doc,
                "entry": entry,
                "section": section,
                "build_meta": doc.build_meta,
                "title": entry.paper_label,
                "body": _entry_body_html(entry),
            })
            counts["entries"] += 1

    # -- beyond contribs + their entries --------------------------------
    for contrib in doc.beyond:
        _emit(env, out, Path("beyond") / f"{contrib.id}.html", "beyond.html", {
            "document": doc,
            "beyond": contrib,         # UI templates name it `beyond`
            "contrib": contrib,        # legacy alias for the placeholder
            "entries": contrib.entries,
            "build_meta": doc.build_meta,
            "title": contrib.title,
            "body": _beyond_body_html(contrib),
        })
        counts["beyond"] += 1
        for entry in contrib.entries:
            _emit(env, out, Path("entries") / f"{entry.id}.html", "entry.html", {
                "document": doc,
                "entry": entry,
                "section": None,
                "contrib": contrib,
                "build_meta": doc.build_meta,
                "title": entry.paper_label,
                "body": _entry_body_html(entry),
            })
            counts["entries"] += 1

    # -- single gaps page ------------------------------------------------
    _emit(env, out, Path("gaps.html"), "gap.html", {
        "document": doc,
        "gaps": doc.gaps,
        "build_meta": doc.build_meta,
        "title": "Not formalised",
        "body": _gaps_body_html(doc.gaps),
    })
    counts["gaps"] = len(doc.gaps)

    return counts


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
                + (f' (<a href="{f.coqdoc_url}">coqdoc</a>)' if f.coqdoc_url else "")
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


def _beyond_body_html(contrib: Any) -> str:
    parts = [contrib.intro_html, "<ul>"]
    for e in contrib.entries:
        parts.append(
            f'<li><a href="../entries/{e.id}.html"><strong>{e.paper_label}</strong></a> '
            f"{_status_pills(e.status)} — {e.statement_html}</li>"
        )
    parts.append("</ul>")
    return "\n".join(parts)
