#!/usr/bin/env python3
"""Build the Icones auditor dashboard from PAPER / PPL / EXAMPLES markdown.

Usage:
    python tools/build_auditor.py \\
        --paper    docs/PAPER.md \\
        --ppl      docs/PPL.md \\
        --examples docs/EXAMPLES.md \\
        --out      site/auditor/ \\
        --coqproject _CoqProject \\
        --github-repo $GITHUB_REPOSITORY \\
        --commit $GITHUB_SHA \\
        [--strict]
"""

from __future__ import annotations

import argparse
import datetime as _dt
import sys
from pathlib import Path

# Make this script runnable both as ``python tools/build_auditor.py`` and
# ``python -m tools.build_auditor`` without the package having to be on
# sys.path.
if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from tools.auditor.coqdoc import CoqdocResolver, parse_coqproject  # noqa: E402
from tools.auditor.parser import parse_three_tabs  # noqa: E402
from tools.auditor.render import render  # noqa: E402
from tools.auditor.xref import linkify_all  # noqa: E402


def _build_argparser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--paper", required=True, help="Path to docs/PAPER.md")
    p.add_argument("--ppl", required=True, help="Path to docs/PPL.md")
    p.add_argument(
        "--examples", required=True, help="Path to docs/EXAMPLES.md"
    )
    p.add_argument("--out", required=True, help="Output directory")
    p.add_argument("--coqproject", default="_CoqProject", help="Path to _CoqProject")
    p.add_argument(
        "--github-repo",
        default="LLM4Rocq/icones-rocq",
        help="GitHub repo for blob links (e.g. LLM4Rocq/icones-rocq)",
    )
    p.add_argument("--commit", default="main", help="Commit SHA for blob links")
    p.add_argument("--coqdoc-base", default="docs/", help="Relative coqdoc base URL")
    p.add_argument(
        "--template-dir",
        default=None,
        help="Override template directory (defaults to the bundled one)",
    )
    p.add_argument(
        "--strict",
        action="store_true",
        help="Treat parser warnings as errors (exit 1 if any).",
    )
    return p


def _build_search_index(out_path: Path) -> str | None:
    """Run the Pagefind indexer over the rendered HTML in ``out_path``.

    Pagefind is a static-site search: it crawls the generated HTML (the main
    content region is marked ``data-pagefind-body``) and writes a search index
    plus the UI bundle to ``out_path/pagefind/``.  The page's app.js then loads
    ``pagefind/pagefind-ui.js`` and initialises the ``#search`` box.

    We use the official ``pagefind`` Python package (a thin wrapper around the
    Rust ``pagefind_extended`` binary).  If it is not installed, we degrade
    gracefully: search simply won't appear, and we surface a clear warning
    rather than failing the build.

    Returns a human-readable warning string if indexing was skipped/failed,
    else ``None`` on success.
    """
    try:
        import asyncio

        from pagefind.index import PagefindIndex
    except Exception as exc:  # noqa: BLE001 — any import failure → degrade.
        return (
            "Pagefind not available (%s); search index NOT built. "
            "Install it with `pip install \"pagefind[extended]\"` to enable "
            "the search bar." % type(exc).__name__
        )

    async def _run() -> dict:
        async with PagefindIndex(
            config={"output_path": str(out_path / "pagefind")}
        ) as index:
            return await index.add_directory(str(out_path))

    try:
        result = asyncio.run(_run())
    except Exception as exc:  # noqa: BLE001 — missing binary, IO, etc.
        return (
            "Pagefind indexing failed (%s: %s); search index NOT built."
            % (type(exc).__name__, exc)
        )

    pages = result.get("page_count") if isinstance(result, dict) else None
    print(f"[build_auditor] pagefind: indexed {pages} page(s) → {out_path}/pagefind/")
    return None


def _tab_counts(doc) -> tuple[int, int, dict[str, int]]:
    """Return (entries, files, status_counts) for a single Document."""
    n_entries = sum(len(s.entries) for s in doc.sections) + sum(
        len(b.entries) for b in doc.beyond
    )
    n_files = sum(len(e.rocq_files) for s in doc.sections for e in s.entries) + sum(
        len(e.rocq_files) for b in doc.beyond for e in b.entries
    )
    status_counts: dict[str, int] = {}
    for s in doc.sections:
        for e in s.entries:
            for st in e.status:
                status_counts[st] = status_counts.get(st, 0) + 1
    for b in doc.beyond:
        for e in b.entries:
            for st in e.status:
                status_counts[st] = status_counts.get(st, 0) + 1
    for _ in doc.gaps:
        status_counts["gap"] = status_counts.get("gap", 0) + 1
    return n_entries, n_files, status_counts


def main(argv: list[str] | None = None) -> int:
    args = _build_argparser().parse_args(argv)
    paper_path = Path(args.paper).resolve()
    ppl_path = Path(args.ppl).resolve()
    examples_path = Path(args.examples).resolve()
    out_path = Path(args.out).resolve()
    project_root = Path(args.coqproject).resolve().parent

    bindings = parse_coqproject(args.coqproject)
    resolver = CoqdocResolver(
        bindings=bindings,
        github_repo=args.github_repo,
        commit=args.commit,
        coqdoc_base=args.coqdoc_base,
    )

    three, warns = parse_three_tabs(
        paper_path=paper_path,
        ppl_path=ppl_path,
        examples_path=examples_path,
        resolver=resolver,
        project_root=project_root,
        strict=args.strict,
    )
    # Global cross-tab + source-line go-to-definition pass.  Each tab's
    # per-document linkify (run inside parse_file) has already wired
    # same-tab entry links; this pass mops up the remaining plain idents
    # by consulting the cross-tab entry map, a theories/ source index and
    # the installed mathcomp sources, so e.g. a PPL snippet's `EM_term`
    # links to its Paper entry page, an undocumented project ident links
    # to its GitHub blob line, and a mathcomp ident (`measurable`,
    # `dirac`, …) links out to mathcomp's versioned online source.
    # ``mathcomp_root=None`` lets linkify_all auto-locate the installed
    # package (and silently skip external links if it is absent).
    linkify_all(
        three,
        resolver=resolver,
        theories_root=project_root / "theories",
        repo_root=project_root,
    )
    # Provenance — shared between tabs at the top-level.
    built_at = _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds")
    three.build_meta.commit = args.commit
    three.build_meta.built_at = built_at
    # `repo` is not a declared BuildMeta field (the dataclass lives in
    # schema.py, which is owned by the parser stream); we stash it as a
    # dynamic attribute so templates can read it as `build_meta.repo`.
    setattr(three.build_meta, "repo", args.github_repo)
    setattr(three.paper.build_meta, "repo", args.github_repo)
    setattr(three.ppl.build_meta, "repo", args.github_repo)
    setattr(three.examples.build_meta, "repo", args.github_repo)
    # Surface the combined source line count for the footer.
    three.build_meta.auditor_lines = (
        three.paper.build_meta.auditor_lines
        + three.ppl.build_meta.auditor_lines
        + three.examples.build_meta.auditor_lines
    )
    # Per-tab build_meta is overridden inside _emit_tab() to match
    # the top-level metadata, so the footer is consistent across pages.

    counts = render(three, out_path, template_dir=args.template_dir)

    # Post-render: build the Pagefind search index over the emitted HTML.
    # This populates ``out/pagefind/`` (index + UI bundle) that the search
    # bar loads at runtime.  A missing/broken Pagefind degrades gracefully:
    # it prints a NOTICE (not a parser warning), so it never fails --strict.
    search_notice = _build_search_index(out_path)
    if search_notice:
        print(f"[build_auditor] NOTICE: {search_notice}", file=sys.stderr)

    p_n, p_f, p_status = _tab_counts(three.paper)
    l_n, l_f, l_status = _tab_counts(three.ppl)
    x_n, x_f, x_status = _tab_counts(three.examples)

    print(f"[build_auditor] wrote {out_path}/")
    print(
        f"[build_auditor] paper:    sections={len(three.paper.sections)} "
        f"beyond={len(three.paper.beyond)} gaps={len(three.paper.gaps)} "
        f"entries={p_n} files={p_f}"
    )
    print(
        f"[build_auditor] ppl:      sections={len(three.ppl.sections)} "
        f"beyond={len(three.ppl.beyond)} gaps={len(three.ppl.gaps)} "
        f"entries={l_n} files={l_f}"
    )
    print(
        f"[build_auditor] examples: sections={len(three.examples.sections)} "
        f"beyond={len(three.examples.beyond)} gaps={len(three.examples.gaps)} "
        f"entries={x_n} files={x_f}"
    )
    print(f"[build_auditor] artefact counts: {counts}")
    print(f"[build_auditor] paper    status distribution: {p_status}")
    print(f"[build_auditor] ppl      status distribution: {l_status}")
    print(f"[build_auditor] examples status distribution: {x_status}")
    if warns:
        print(f"[build_auditor] {len(warns)} warning(s):", file=sys.stderr)
        for w in warns:
            print(f"  - {w}", file=sys.stderr)
        if args.strict:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
