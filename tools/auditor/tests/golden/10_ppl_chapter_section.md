# Goldens — PPL-shape chapter (prose + snippets, no table)

## Beyond the paper — The widget language

A miniature surface language used by the auditor parser test.

### Types and contexts (`ppl_type`, `named_ctx`)

The `ppl_type` inductive enumerates the surface types.  Each one is
mapped to an ICones object by the type-translation pass.

```coq
(* theories/programs/ppl.v *)
Inductive ppl_type : Type :=
  | tunit
  | tbase (X : ar_obj Ar)
  | tprod (t1 t2 : ppl_type).
```

`drop_names` forgets identifiers and exposes the underlying typing
context.

### Free-coalgebra types (`is_free_coalg_type`)

A purely syntactic predicate gating the `ne_fix_mr` constructor.

```coq
(* theories/programs/ppl.v *)
Fixpoint is_free_coalg_type (t : ppl_type) : bool :=
  match t with
  | tfun _ _ => true
  | tprod t1 t2 => is_free_coalg_type t1 && is_free_coalg_type t2
  | _ => false
  end.
```
