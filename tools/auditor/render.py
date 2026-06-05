"""Jinja2 driver that emits the static-site artefacts under ``site/auditor/``.

The template lookup order is:
    1. The directory passed as ``template_dir`` (defaults to
       ``tools/auditor/templates/``).
    2. The bundled placeholder ``__placeholder.html`` if a specific
       template is missing.

Per-template context contracts (the contract with the UI agent):

``index.html``    : ``{document, sections, beyond, gaps, axiom_anchors, build_meta}``
``section.html``  : ``{document, section, entries, build_meta}``
``entry.html``    : ``{document, entry, section, build_meta}``
``beyond.html``   : ``{document, contrib, entries, build_meta}``
``gap.html``      : ``{document, gap, build_meta}``

The placeholder template uses only ``{title, body, build_meta}`` and is
substituted for any missing template.
"""

from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path
from typing import Any

from jinja2 import ChoiceLoader, Environment, FileSystemLoader, TemplateNotFound, select_autoescape
from pygments.formatters import HtmlFormatter

from .schema import Document


BUNDLED_TEMPLATE_DIR = Path(__file__).parent / "templates"
PLACEHOLDER_NAME = "__placeholder.html"


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

    # -- data.json (canonical export) ------------------------------------
    payload = asdict(doc)
    (out / "data.json").write_text(json.dumps(payload, indent=2), encoding="utf-8")
    counts["json"] = 1

    # -- index -----------------------------------------------------------
    index_ctx = {
        "document": doc,
        "sections": doc.sections,
        "beyond": doc.beyond,
        "gaps": doc.gaps,
        "axiom_anchors": doc.axiom_anchors,
        "build_meta": doc.build_meta,
        "title": "Index",
        "body": _summary_html(doc),
    }
    (out / "index.html").write_text(
        _render_template(env, "index.html", index_ctx), encoding="utf-8"
    )
    counts["index"] = 1

    # -- per-section -----------------------------------------------------
    for section in doc.sections:
        d = out / "section" / section.id
        d.mkdir(parents=True, exist_ok=True)
        ctx = {
            "document": doc,
            "section": section,
            "entries": section.entries,
            "build_meta": doc.build_meta,
            "title": section.title or section.id,
            "body": _section_body_html(section),
        }
        (d / "index.html").write_text(
            _render_template(env, "section.html", ctx), encoding="utf-8"
        )
        counts["sections"] += 1

        for entry in section.entries:
            ed = out / "entry" / entry.id
            ed.mkdir(parents=True, exist_ok=True)
            ectx = {
                "document": doc,
                "entry": entry,
                "section": section,
                "build_meta": doc.build_meta,
                "title": entry.paper_label,
                "body": _entry_body_html(entry),
            }
            (ed / "index.html").write_text(
                _render_template(env, "entry.html", ectx), encoding="utf-8"
            )
            counts["entries"] += 1

    # -- beyond ----------------------------------------------------------
    for contrib in doc.beyond:
        d = out / "beyond" / contrib.id
        d.mkdir(parents=True, exist_ok=True)
        ctx = {
            "document": doc,
            "contrib": contrib,
            "entries": contrib.entries,
            "build_meta": doc.build_meta,
            "title": contrib.title,
            "body": _beyond_body_html(contrib),
        }
        (d / "index.html").write_text(
            _render_template(env, "beyond.html", ctx), encoding="utf-8"
        )
        counts["beyond"] += 1
        # Each beyond entry also gets a per-entry detail page.
        for entry in contrib.entries:
            ed = out / "entry" / entry.id
            ed.mkdir(parents=True, exist_ok=True)
            ectx = {
                "document": doc,
                "entry": entry,
                "section": None,
                "contrib": contrib,
                "build_meta": doc.build_meta,
                "title": entry.paper_label,
                "body": _entry_body_html(entry),
            }
            (ed / "index.html").write_text(
                _render_template(env, "entry.html", ectx), encoding="utf-8"
            )
            counts["entries"] += 1

    # -- gaps ------------------------------------------------------------
    for gap in doc.gaps:
        d = out / "gap" / gap.id
        d.mkdir(parents=True, exist_ok=True)
        ctx = {
            "document": doc,
            "gap": gap,
            "build_meta": doc.build_meta,
            "title": gap.paper_label,
            "body": gap.description_html + "<hr>" + gap.reason_html,
        }
        (d / "index.html").write_text(
            _render_template(env, "gap.html", ctx), encoding="utf-8"
        )
        counts["gaps"] += 1

    # -- pygments stylesheet (so highlighted snippets render) ------------
    css = HtmlFormatter(cssclass="highlight coq").get_style_defs(".highlight")
    static = out / "static"
    static.mkdir(parents=True, exist_ok=True)
    (static / "pygments.css").write_text(css, encoding="utf-8")
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
            f'<li><a href="section/{s.id}/">{s.paper_section}</a> — '
            f"{len(s.entries)} entries</li>"
        )
    rows.append("</ul>")
    rows.append("<p>Beyond:</p><ul>")
    for b in doc.beyond:
        rows.append(
            f'<li><a href="beyond/{b.id}/">{b.title}</a> — '
            f"{len(b.entries)} entries</li>"
        )
    rows.append("</ul>")
    if doc.gaps:
        rows.append("<p>Gaps:</p><ul>")
        for g in doc.gaps:
            rows.append(f'<li><a href="gap/{g.id}/">{g.paper_label}</a></li>')
        rows.append("</ul>")
    return "\n".join(rows)


def _section_body_html(section: Any) -> str:
    parts = [section.intro_html, "<ul>"]
    for e in section.entries:
        parts.append(
            f'<li><a href="../../entry/{e.id}/"><strong>{e.paper_label}</strong></a> '
            f"{_status_pills(e.status)} — {e.statement_html}</li>"
        )
    parts.append("</ul>")
    if section.notes_html:
        parts.append('<div class="note">' + section.notes_html + "</div>")
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
            f'<li><a href="../../entry/{e.id}/"><strong>{e.paper_label}</strong></a> '
            f"{_status_pills(e.status)} — {e.statement_html}</li>"
        )
    parts.append("</ul>")
    return "\n".join(parts)
