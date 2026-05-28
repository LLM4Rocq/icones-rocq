#!/usr/bin/env bash
# verify.sh — canonical axiom-freeness check for the Icones development.
#
# Confirms that the headline results — and hence the whole linear-logic
# model through paper §9 — depend on ONLY the three classical-logic
# axioms inherited from mathcomp-analysis (boolp), and on NO
# project-specific axioms.
#
# Usage:  ./verify.sh
#
# Does:
#   1. Clean rebuild (`make clean && make -j`).
#   2. `Print Assumptions` on the headline theorems.
#
# Expected output: each result lists ONLY the three classical axioms
#   boolp.functional_extensionality_dep
#   boolp.propositional_extensionality
#   boolp.constructive_indefinite_description
# and nothing else — no project-specific `Axiom`/`Parameter`, and (note)
# NO `Prop_irrelevance`.

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
echo "=== Print Assumptions (headline results) ==="
# Feed the commands on stdin to the Rocq toplevel (there is no `-e`
# batch flag). Modules are loaded via `Require Import` of the
# already-compiled .vo, so this is fast.
cmd='From Icones.kernels Require Import kernel_embedding.
From Icones.homs Require Import smcc bang seely coalgebra.
Print Assumptions Skern_to_ICones_fully_faithful.  (* Thm 6.5  — the anchor *)
Print Assumptions ICones_smcc.                      (* Thm 5.15 — SMCC *)
Print Assumptions Bang_comonad.                     (* the ! exponential comonad *)
Print Assumptions ICones_Seely.                     (* Thm 9.5  — Seely category *)
Print Assumptions Coalg_counit.                     (* Thm 9.7  — FMeas coalgebra *)
Print Assumptions Coalg_coassoc.'
if command -v rocq >/dev/null 2>&1; then
  printf '%s\n' "$cmd" | rocq repl -q -Q theories Icones
else
  printf '%s\n' "$cmd" | coqtop -q -Q theories Icones
fi

echo
echo "Verification complete."
