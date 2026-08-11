#!/usr/bin/env python3
"""Import-layer checker for the Icones development.

WHY THIS EXISTS
===============
``theories/`` is stratified into layers.  The stratification is not a
naming convention: it is the reason the development can be read (and
rebuilt) bottom-up, and the reason ``homs`` (the symmetric monoidal
closed structure) and ``stable`` (stable maps / scones) can be developed
independently of one another.  Nothing in Rocq enforces it — a single
stray ``Require`` silently welds two layers together and the next reader
has no way to tell that the boundary ever existed.

This script re-derives the layer of every ``theories/**/*.v`` file from
its directory, reads every ``Require`` edge out of it, and fails when an
edge points at a layer that is not strictly below (or equal to) the
importing file's own layer.

THE LAYERS
==========
Lower rank = closer to the base.  Directories sharing a rank are
**parallel**: they may both import everything below, and neither may
import the other.

    0  prelude                 classical/order-theoretic scaffolding
    1  cones                   cones, the cone category
    2  mcones                  measurable cones
    3  icones                  integrable cones, Pettis integral
    4  homs | stable           SMCC hom-structure || stable maps, scones
    5  kernels | exp           s-finite kernels   || the ! exponential, Seely
    6  cbv                     Eilenberg-Moore category, CBV leaves
    7  programs                the PPL layer

Two rules are checked:

``below``
    an edge from rank ``i`` to rank ``j`` is legal iff ``j <= i``;

``parallel``
    an edge between two *different* directories of the *same* rank is
    illegal.  That is what "parallel" means: ``homs`` never imports
    ``stable`` and ``stable`` never imports ``homs``; likewise for
    ``kernels`` and ``exp``.

Intra-directory edges are always legal; acyclicity within a directory is
already guaranteed by ``coqdep`` at build time.

USAGE
=====
    python3 tools/check_layers.py            # exit 1 on any violation
    python3 tools/check_layers.py --list     # print the layer of each file
    python3 tools/check_layers.py --graph    # print every cross-layer edge

Run from the repository root (or pass ``--root``).
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

# --------------------------------------------------------------------------
# The layer assignment.  Each entry is one rank; the directories inside a
# rank are parallel to each other.
# --------------------------------------------------------------------------
LAYERS: list[tuple[str, ...]] = [
    ("prelude",),
    ("cones",),
    ("mcones",),
    ("icones",),
    ("homs", "stable"),
    ("kernels", "exp"),
    ("cbv",),
    ("programs",),
]

RANK: dict[str, int] = {d: i for i, ds in enumerate(LAYERS) for d in ds}

# ``Require`` in any of its spellings, including the bare
# ``Require Icones.foo.bar.`` with no Import/Export, and the
# multi-module ``Require Import Icones.a.b Icones.c.d.`` form.  The
# ``From X Require Import y`` form is matched separately.
_REQUIRE_RE = re.compile(
    r"(?<![\w.])Require\s+(?:Import\s+|Export\s+)?"
    r"((?:Icones\.[\w.]+\s*)+)"
)
_FROM_RE = re.compile(
    r"(?<![\w.])From\s+(Icones(?:\.[\w]+)*)\s+Require\s+"
    r"(?:Import\s+|Export\s+)?([\w.\s]+?)\s*\."
)

# ``(* ... *)`` comments, non-nesting approximation good enough to keep a
# commented-out Require or a coqdoc citation from counting as an edge.
_COMMENT_RE = re.compile(r"\(\*.*?\*\)", re.DOTALL)


def strip_comments(src: str) -> str:
    """Blank out ``(* ... *)`` blocks, preserving line structure."""
    def blank(m: re.Match[str]) -> str:
        return re.sub(r"[^\n]", " ", m.group(0))

    prev = None
    out = src
    # Rocq comments nest; iterate the non-nesting regex to convergence so a
    # nested comment cannot leave a dangling ``*)`` behind.
    while prev != out:
        prev = out
        out = _COMMENT_RE.sub(blank, out)
    return out


def module_of(path: Path, theories: Path) -> str:
    rel = path.relative_to(theories).with_suffix("")
    return "Icones." + ".".join(rel.parts)


def directory_of(module: str) -> str | None:
    """``Icones.homs.linhom`` -> ``homs``; ``Icones.programs.infra.x`` -> ``programs``."""
    parts = module.split(".")
    if len(parts) < 2 or parts[0] != "Icones":
        return None
    return parts[1]


def requires_of(src: str) -> set[str]:
    """Every ``Icones.*`` module this source Requires."""
    src = strip_comments(src)
    deps: set[str] = set()
    for m in _REQUIRE_RE.finditer(src):
        for tok in m.group(1).split():
            tok = tok.rstrip(".")
            if tok.startswith("Icones."):
                deps.add(tok)
    for m in _FROM_RE.finditer(src):
        prefix = m.group(1)
        for name in m.group(2).split():
            deps.add(f"{prefix}.{name}")
    return deps


def collect(theories: Path) -> dict[str, tuple[Path, set[str]]]:
    files: dict[str, tuple[Path, set[str]]] = {}
    for p in sorted(theories.rglob("*.v")):
        files[module_of(p, theories)] = (p, requires_of(p.read_text(encoding="utf-8")))
    return files


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", default=".", help="repository root (default: cwd)")
    ap.add_argument("--list", action="store_true", help="print each file's layer")
    ap.add_argument("--graph", action="store_true",
                    help="print the directory-level edge summary")
    args = ap.parse_args(argv)

    root = Path(args.root).resolve()
    theories = root / "theories"
    if not theories.is_dir():
        print(f"check_layers: no theories/ under {root}", file=sys.stderr)
        return 2

    files = collect(theories)

    # Every directory that actually exists must have a declared rank —
    # otherwise a new directory would silently escape the check.
    unknown = sorted({directory_of(m) for m in files} - set(RANK) - {None})
    if unknown:
        print("check_layers: FAIL — directories with no declared layer: "
              + ", ".join(str(u) for u in unknown), file=sys.stderr)
        print("  add them to LAYERS in tools/check_layers.py", file=sys.stderr)
        return 1

    if args.list:
        for m in sorted(files, key=lambda m: (RANK[directory_of(m)], m)):
            print(f"{RANK[directory_of(m)]}  {directory_of(m):9s} {m}")
        return 0

    violations: list[str] = []
    dangling: list[str] = []
    cross: dict[tuple[str, str], int] = {}

    for mod in sorted(files):
        path, deps = files[mod]
        src_dir = directory_of(mod)
        src_rank = RANK[src_dir]
        rel = path.relative_to(root)
        for dep in sorted(deps):
            if dep not in files:
                dangling.append(f"{rel}: Require of unknown module {dep}")
                continue
            dst_dir = directory_of(dep)
            dst_rank = RANK[dst_dir]
            if dst_rank > src_rank:
                violations.append(
                    f"{rel}: [{src_dir} = layer {src_rank}] imports {dep} "
                    f"[{dst_dir} = layer {dst_rank}] — upward edge")
            elif dst_rank == src_rank and dst_dir != src_dir:
                violations.append(
                    f"{rel}: [{src_dir}] imports {dep} [{dst_dir}] — "
                    f"{src_dir} and {dst_dir} are parallel at layer {src_rank}")
            else:
                key = (src_dir, dst_dir)
                cross[key] = cross.get(key, 0) + 1

    if args.graph:
        for (a, b), n in sorted(cross.items(),
                                key=lambda kv: (RANK[kv[0][0]], kv[0][0],
                                                RANK[kv[0][1]], kv[0][1])):
            kind = "self " if a == b else "down "
            print(f"{kind}{a:9s} -> {b:9s} {n:4d} edge(s)")
        return 0

    for d in dangling:
        print(f"check_layers: FAIL — {d}", file=sys.stderr)
    for v in violations:
        print(f"check_layers: FAIL — {v}", file=sys.stderr)

    if violations or dangling:
        print(f"check_layers: {len(violations) + len(dangling)} violation(s) "
              f"in {len(files)} file(s)", file=sys.stderr)
        return 1

    edges = sum(len(d) for _, d in files.values())
    print(f"check_layers: OK — {len(files)} file(s), {edges} import edge(s), "
          f"{len(LAYERS)} layers, 0 violations")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
