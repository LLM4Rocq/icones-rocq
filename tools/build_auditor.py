#!/usr/bin/env python3
"""Build the Icones auditor dashboard from ``AUDITOR.md``.

Usage:
    python tools/build_auditor.py \\
        --input AUDITOR.md \\
        --out site/auditor/ \\
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
from tools.auditor.parser import parse_file  # noqa: E402
from tools.auditor.render import render  # noqa: E402


def _build_argparser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", required=True, help="Path to AUDITOR.md")
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


def main(argv: list[str] | None = None) -> int:
    args = _build_argparser().parse_args(argv)
    in_path = Path(args.input).resolve()
    out_path = Path(args.out).resolve()
    project_root = Path(args.coqproject).resolve().parent

    bindings = parse_coqproject(args.coqproject)
    resolver = CoqdocResolver(
        bindings=bindings,
        github_repo=args.github_repo,
        commit=args.commit,
        coqdoc_base=args.coqdoc_base,
    )

    doc, warns = parse_file(
        in_path,
        resolver=resolver,
        project_root=project_root,
        strict=args.strict,
    )
    # Provenance.
    doc.build_meta.commit = args.commit
    doc.build_meta.built_at = _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds")

    counts = render(doc, out_path, template_dir=args.template_dir)

    n_entries = sum(len(s.entries) for s in doc.sections) + sum(
        len(b.entries) for b in doc.beyond
    )
    n_files = sum(len(e.rocq_files) for s in doc.sections for e in s.entries) + sum(
        len(e.rocq_files) for b in doc.beyond for e in b.entries
    )

    # Status distribution.
    status_counts: dict[str, int] = {}
    for s in doc.sections:
        for e in s.entries:
            for st in e.status:
                status_counts[st] = status_counts.get(st, 0) + 1
    for b in doc.beyond:
        for e in b.entries:
            for st in e.status:
                status_counts[st] = status_counts.get(st, 0) + 1
    for g in doc.gaps:
        status_counts["gap"] = status_counts.get("gap", 0) + 1

    print(f"[build_auditor] wrote {out_path}/")
    print(
        f"[build_auditor] sections={len(doc.sections)} beyond={len(doc.beyond)} "
        f"gaps={len(doc.gaps)} entries={n_entries} files={n_files}"
    )
    print(f"[build_auditor] artefact counts: {counts}")
    print(f"[build_auditor] status distribution: {status_counts}")
    if warns:
        print(f"[build_auditor] {len(warns)} warning(s):", file=sys.stderr)
        for w in warns:
            print(f"  - {w}", file=sys.stderr)
        if args.strict:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
