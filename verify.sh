#!/usr/bin/env bash
# verify.sh — canonical verification of the MVP headline
# `Skern_to_ICones_fully_faithful` (paper Theorem 6.5) against a
# fresh build.
#
# Usage:  ./verify.sh
#
# Does:
#   1. Clean rebuild (`make clean && make -j`).
#   2. `Print Assumptions Icones.kernels.thm65.Skern_to_ICones_fully_faithful`.
#
# Expected output: only the classical-logic axioms inherited from
# mathcomp-analysis (`boolp.functional_extensionality_dep`,
# `boolp.propositional_extensionality`, `boolp.constructive_indefinite_description`,
# `Prop_irrelevance`). No project-specific axioms.

set -e
cd "$(dirname "$0")"

if [ ! -f Makefile.coq ]; then
  if command -v rocq >/dev/null 2>&1; then
    rocq makefile -f _CoqProject -o Makefile.coq
  else
    coq_makefile -f _CoqProject -o Makefile.coq
  fi
fi

echo "=== Clean rebuild ==="
make -f Makefile.coq clean
make -f Makefile.coq -j

echo
echo "=== Print Assumptions Skern_to_ICones_fully_faithful ==="
# Feed the command on stdin to the Rocq toplevel (there is no `-e`
# batch flag). The module is loaded via `Require Import` of the
# already-compiled .vo, so this is fast.
cmd='From Icones.kernels Require Import thm65.
Print Assumptions Skern_to_ICones_fully_faithful.'
if command -v rocq >/dev/null 2>&1; then
  printf '%s\n' "$cmd" | rocq repl -q -Q theories Icones
else
  printf '%s\n' "$cmd" | coqtop -q -Q theories Icones
fi

echo
echo "Verification complete."
