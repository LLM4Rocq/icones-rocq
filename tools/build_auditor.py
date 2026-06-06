#!/usr/bin/env python3
"""Build the Icones auditor dashboard from ``docs/PAPER.md`` + ``docs/PPL.md``.

Usage:
    python tools/build_auditor.py \\
        --paper docs/PAPER.md \\
        --ppl   docs/PPL.md \\
        --out   site/auditor/ \\
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
from tools.auditor.parser import parse_two_tabs  # noqa: E402
from tools.auditor.render import render  # noqa: E402


def _build_argparser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--paper", required=True, help="Path to docs/PAPER.md")
    p.add_argument("--ppl", required=True, help="Path to docs/PPL.md")
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
    out_path = Path(args.out).resolve()
    project_root = Path(args.coqproject).resolve().parent

    bindings = parse_coqproject(args.coqproject)
    resolver = CoqdocResolver(
        bindings=bindings,
        github_repo=args.github_repo,
        commit=args.commit,
        coqdoc_base=args.coqdoc_base,
    )

    two, warns = parse_two_tabs(
        paper_path=paper_path,
        ppl_path=ppl_path,
        resolver=resolver,
        project_root=project_root,
        strict=args.strict,
    )
    # Provenance — shared between tabs at the top-level.
    built_at = _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds")
    two.build_meta.commit = args.commit
    two.build_meta.built_at = built_at
    # `repo` is not a declared BuildMeta field (the dataclass lives in
    # schema.py, which is owned by the parser stream); we stash it as a
    # dynamic attribute so templates can read it as `build_meta.repo`.
    setattr(two.build_meta, "repo", args.github_repo)
    setattr(two.paper.build_meta, "repo", args.github_repo)
    setattr(two.ppl.build_meta, "repo", args.github_repo)
    # Surface the combined source line count for the footer.
    two.build_meta.auditor_lines = (
        two.paper.build_meta.auditor_lines + two.ppl.build_meta.auditor_lines
    )
    # Per-tab build_meta is overridden inside _emit_tab() to match
    # the top-level metadata, so the footer is consistent across pages.

    counts = render(two, out_path, template_dir=args.template_dir)

    p_n, p_f, p_status = _tab_counts(two.paper)
    l_n, l_f, l_status = _tab_counts(two.ppl)

    print(f"[build_auditor] wrote {out_path}/")
    print(
        f"[build_auditor] paper: sections={len(two.paper.sections)} "
        f"beyond={len(two.paper.beyond)} gaps={len(two.paper.gaps)} "
        f"entries={p_n} files={p_f}"
    )
    print(
        f"[build_auditor] ppl:   sections={len(two.ppl.sections)} "
        f"beyond={len(two.ppl.beyond)} gaps={len(two.ppl.gaps)} "
        f"entries={l_n} files={l_f}"
    )
    print(f"[build_auditor] artefact counts: {counts}")
    print(f"[build_auditor] paper status distribution: {p_status}")
    print(f"[build_auditor] ppl   status distribution: {l_status}")
    if warns:
        print(f"[build_auditor] {len(warns)} warning(s):", file=sys.stderr)
        for w in warns:
            print(f"  - {w}", file=sys.stderr)
        if args.strict:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
