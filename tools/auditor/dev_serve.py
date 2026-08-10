#!/usr/bin/env python3
"""Render the auditor dashboard from a data.json file, then serve it.

Usage:
    python tools/auditor/dev_serve.py [data.json] [--out DIR] [--port N] [--no-serve]

When invoked without arguments, expects a data.json on stdin or at
`tools/auditor/_dev_data.json`. The output directory defaults to
`_site/auditor/`. The static/ tree is copied verbatim alongside templates.

The script auto-detects whether the payload is the triple-tab shape
(``{"paper": ..., "ppl": ..., "examples": ...}``), the legacy dual-tab
shape (``{"paper": ..., "ppl": ...}``) — in which case an empty Examples
tab is synthesised — or the legacy single-Document shape, and emits
accordingly.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import socketserver
import sys
from http.server import SimpleHTTPRequestHandler
from pathlib import Path

from jinja2 import Environment, FileSystemLoader, select_autoescape

ROOT = Path(__file__).resolve().parent
TEMPLATES = ROOT / "templates"
STATIC = ROOT / "static"


def xref_href(prefix: str, tab: str = ""):
    """Dev-server mirror of :func:`tools.auditor.render._xref_href`.

    Kept in step with the production resolver for the ``uses`` / ``used-by``
    relation kinds — the per-card "Uses / Used by" navigation panel — so a
    dev preview exercises the same links the deployed site serves.  A
    cross-tab target (``xref['tab']`` differing from the page's tab) climbs
    out of the current tab; the canonical-section collapsing that the real
    renderer applies has no equivalent here (dev_serve emits an entry page
    for every entry), so relation refs always route to ``entries/``.
    """

    def _h(xref):
        kind = xref.get("kind")
        tgt = xref.get("target", "")
        if kind in ("uses", "used-by"):
            xtab = xref.get("tab", "")
            if xtab and tab and xtab != tab:
                return f"{prefix}../{xtab}/entries/{tgt}.html"
            return f"{prefix}entries/{tgt}.html"
        if kind == "section":
            return f"{prefix}sections/{tgt}.html"
        if kind == "entry":
            return f"{prefix}entries/{tgt}.html"
        if kind == "chapter":
            return f"{prefix}chapters/{tgt}.html"
        if kind == "beyond":
            if tgt == "beyond":
                return f"{prefix}index.html#beyond"
            return f"{prefix}beyond/{tgt}.html"
        if kind == "blueprint":
            return f"{prefix}../../blueprint/web/{tgt}"
        return "#" + tgt
    return _h


def _is_multi_tab(data: dict) -> bool:
    """True for both legacy dual-tab and current triple-tab payloads."""
    return "paper" in data and "ppl" in data and "sections" not in data


def _empty_doc() -> dict:
    """Stand-in for a missing tab (e.g. legacy dual-tab payload)."""
    return {
        "preamble_html": "",
        "sections": [],
        "beyond": [],
        "gaps": [],
        "verify_instructions_html": "",
        "axiom_anchors": {"regression": "", "headlines": []},
        "build_meta": {"commit": "", "built_at": "", "auditor_lines": 0},
    }


def _make_env() -> Environment:
    env = Environment(
        loader=FileSystemLoader(str(TEMPLATES)),
        autoescape=select_autoescape(["html", "xml"]),
        trim_blocks=True,
        lstrip_blocks=True,
    )
    env.tests["contains"] = lambda seq, item: item in (seq or [])
    return env


def _set_prefixes(env: Environment, root_prefix: str, static_prefix: str,
                  tab_prefix: str, tab: str = "") -> dict:
    resolver = xref_href(root_prefix, tab)
    env.globals["root_prefix"] = root_prefix
    env.globals["static_prefix"] = static_prefix
    env.globals["tab_prefix"] = tab_prefix
    env.globals["xref_href"] = resolver
    return {
        "root_prefix": root_prefix,
        "static_prefix": static_prefix,
        "tab_prefix": tab_prefix,
        "xref_href": resolver,
    }


def _render_tab(env: Environment, out_dir: Path, tab: str, data: dict,
                build_meta: dict) -> None:
    """Render one tab subtree under ``out_dir/<tab>/``."""
    tab_dir = out_dir / tab
    # Inject shared build_meta onto the doc.
    data = {**data, "build_meta": build_meta}

    base_ctx = {"document": data, "tab": tab, "build_meta": build_meta}

    def render(template_name: str, dest: Path, ctx: dict) -> None:
        dest.parent.mkdir(parents=True, exist_ok=True)
        rel_to_tab = dest.relative_to(tab_dir)
        depth_in_tab = len(rel_to_tab.parts) - 1
        depth_total = len(rel_to_tab.parts)
        root_prefix = "../" * depth_in_tab if depth_in_tab else ""
        static_prefix = "../" * depth_total
        tab_prefix = static_prefix
        prefixes = _set_prefixes(env, root_prefix, static_prefix, tab_prefix, tab)
        ctx = {**ctx, **prefixes}
        html = env.get_template(template_name).render(**ctx)
        dest.write_text(html, encoding="utf-8")

    # Per-tab data.json export.
    (tab_dir).mkdir(parents=True, exist_ok=True)
    (tab_dir / "data.json").write_text(json.dumps(data, indent=2), encoding="utf-8")

    render("index.html", tab_dir / "index.html", base_ctx)
    for section in data.get("sections", []):
        render("section.html", tab_dir / "sections" / f"{section['id']}.html",
               {**base_ctx, "section": section})
        for entry in section["entries"]:
            render("entry.html", tab_dir / "entries" / f"{entry['id']}.html",
                   {**base_ctx, "section": section, "entry": entry})
    for b in data.get("beyond", []):
        render("beyond.html", tab_dir / "beyond" / f"{b['id']}.html",
               {**base_ctx, "beyond": b})
        for entry in b.get("entries", []):
            # beyond.entries from dev_mock are summary dicts without an `id`;
            # skip rendering individual entry pages for them.
            if "id" not in entry:
                continue
            render("entry.html", tab_dir / "entries" / f"{entry['id']}.html",
                   {**base_ctx, "section": None, "contrib": b, "entry": entry})
    render("gap.html", tab_dir / "gaps.html",
           {**base_ctx, "gaps": data.get("gaps", [])})


def build(data: dict, out_dir: Path) -> None:
    env = _make_env()
    out_dir.mkdir(parents=True, exist_ok=True)
    static_out = out_dir / "static"
    if static_out.exists():
        shutil.rmtree(static_out)
    shutil.copytree(STATIC, static_out)

    if _is_multi_tab(data):
        build_meta = data.get("build_meta", {})
        # Legacy dual-tab payloads get an empty Examples tab.
        examples_doc = data.get("examples") or _empty_doc()
        full_payload = {**data, "examples": examples_doc}
        # Combined data.json at the site root.
        (out_dir / "data.json").write_text(
            json.dumps(full_payload, indent=2), encoding="utf-8"
        )
        # Root landing.
        prefixes = _set_prefixes(env, "", "", "")
        root_ctx = {
            "document": data.get("paper", {}),
            "paper": data["paper"],
            "ppl": data["ppl"],
            "examples": examples_doc,
            "build_meta": build_meta,
            "tab": None,
            **prefixes,
        }
        (out_dir / "index.html").write_text(
            env.get_template("root.html").render(**root_ctx),
            encoding="utf-8",
        )
        _render_tab(env, out_dir, "paper", data["paper"], build_meta)
        _render_tab(env, out_dir, "ppl", data["ppl"], build_meta)
        _render_tab(env, out_dir, "examples", examples_doc, build_meta)
        return

    # Legacy single-tab payload: render at the root for back-compat.
    build_meta = data.get("build_meta", {})
    prefixes = _set_prefixes(env, "", "", "")
    base_ctx = {"document": data, "tab": None, "build_meta": build_meta, **prefixes}

    def render(template_name: str, dest: Path, ctx: dict) -> None:
        dest.parent.mkdir(parents=True, exist_ok=True)
        depth = len(dest.relative_to(out_dir).parts) - 1
        prefix = "../" * depth if depth else ""
        prefixes = _set_prefixes(env, prefix, prefix, prefix)
        html = env.get_template(template_name).render(**{**ctx, **prefixes})
        dest.write_text(html, encoding="utf-8")

    render("index.html", out_dir / "index.html", base_ctx)
    for section in data["sections"]:
        render("section.html", out_dir / "sections" / f"{section['id']}.html",
               {**base_ctx, "section": section})
        for entry in section["entries"]:
            render("entry.html", out_dir / "entries" / f"{entry['id']}.html",
                   {**base_ctx, "section": section, "entry": entry})
    for b in data.get("beyond", []):
        render("beyond.html", out_dir / "beyond" / f"{b['id']}.html",
               {**base_ctx, "beyond": b})
    render("gap.html", out_dir / "gaps.html",
           {**base_ctx, "gaps": data.get("gaps", [])})


def serve(out_dir: Path, port: int) -> None:
    os.chdir(out_dir)

    class Handler(SimpleHTTPRequestHandler):
        def log_message(self, fmt, *args):
            sys.stderr.write("[%s] %s\n" % (self.address_string(), fmt % args))

    with socketserver.TCPServer(("127.0.0.1", port), Handler) as httpd:
        sys.stderr.write(f"Serving auditor dashboard at http://127.0.0.1:{port}/\n")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            sys.stderr.write("\nbye.\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("data", nargs="?", help="path to data.json (or '-' for stdin)")
    ap.add_argument("--out", default="_site/auditor", help="output directory")
    ap.add_argument("--port", type=int, default=8123, help="HTTP port")
    ap.add_argument("--no-serve", action="store_true", help="render only, do not serve")
    args = ap.parse_args()

    if args.data is None:
        cand = ROOT / "_dev_data.json"
        if not cand.exists():
            ap.error("no data.json given and no _dev_data.json in tools/auditor/")
        data_text = cand.read_text(encoding="utf-8")
    elif args.data == "-":
        data_text = sys.stdin.read()
    else:
        data_text = Path(args.data).read_text(encoding="utf-8")

    data = json.loads(data_text)
    out_dir = Path(args.out).resolve()
    build(data, out_dir)
    sys.stderr.write(f"Rendered to {out_dir}/\n")
    if args.no_serve:
        return 0
    serve(out_dir, args.port)
    return 0


if __name__ == "__main__":
    sys.exit(main())
