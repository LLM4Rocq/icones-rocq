#!/usr/bin/env python3
"""Render the auditor dashboard from a data.json file, then serve it.

Usage:
    python tools/auditor/dev_serve.py [data.json] [--out DIR] [--port N] [--no-serve]

When invoked without arguments, expects a data.json on stdin or at
`tools/auditor/_dev_data.json`. The output directory defaults to
`_site/auditor/`. The static/ tree is copied verbatim alongside templates.
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


def xref_href(prefix: str):
    def _h(xref):
        kind = xref.get("kind")
        tgt = xref.get("target", "")
        if kind == "section":
            return f"{prefix}sections/{tgt}.html"
        if kind == "entry":
            return f"{prefix}entries/{tgt}.html"
        if kind == "beyond":
            return f"{prefix}beyond/{tgt}.html"
        if kind == "blueprint":
            return f"../blueprint/web/{tgt}"
        return "#" + tgt
    return _h


def build(data: dict, out_dir: Path) -> None:
    env = Environment(
        loader=FileSystemLoader(str(TEMPLATES)),
        autoescape=select_autoescape(["html", "xml"]),
        trim_blocks=True,
        lstrip_blocks=True,
    )
    # selectattr(..., 'contains', 'x') — convenient for testing list membership.
    env.tests["contains"] = lambda seq, item: item in (seq or [])

    out_dir.mkdir(parents=True, exist_ok=True)
    # Copy static assets.
    static_out = out_dir / "static"
    if static_out.exists():
        shutil.rmtree(static_out)
    shutil.copytree(STATIC, static_out)

    def render(template_name: str, dest: Path, ctx: dict) -> None:
        dest.parent.mkdir(parents=True, exist_ok=True)
        # `root_prefix` and `static_prefix` are relative paths back to the
        # site root from `dest`, so the static layout works both when served
        # from a subdirectory and when opened via file://.
        depth = len(dest.relative_to(out_dir).parts) - 1
        prefix = "../" * depth if depth else ""
        # Patch the env globals so macros see the helpers without us having
        # to thread them through every macro call. Render is single-threaded.
        env.globals["root_prefix"] = prefix
        env.globals["static_prefix"] = prefix
        env.globals["xref_href"] = xref_href(prefix)
        ctx = {
            **ctx,
            "root_prefix": prefix,
            "static_prefix": prefix,
            "xref_href": xref_href(prefix),
        }
        html = env.get_template(template_name).render(**ctx)
        dest.write_text(html, encoding="utf-8")

    base_ctx = {"document": data}

    # Index.
    render("index.html", out_dir / "index.html", base_ctx)

    # Section pages.
    for section in data["sections"]:
        render("section.html", out_dir / "sections" / f"{section['id']}.html",
               {**base_ctx, "section": section})
        # Per-entry pages.
        for entry in section["entries"]:
            render("entry.html", out_dir / "entries" / f"{entry['id']}.html",
                   {**base_ctx, "section": section, "entry": entry})

    # Beyond pages.
    for b in data.get("beyond", []):
        render("beyond.html", out_dir / "beyond" / f"{b['id']}.html",
               {**base_ctx, "beyond": b})

    # Single gap page.
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
