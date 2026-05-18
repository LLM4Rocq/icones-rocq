(** * Classical-logic extras

    Thin re-exports of [boolp] tools used throughout Icones, with a couple
    of one-line helper lemmas. No content from the paper.

    Paper reference: footnotes in §1.1 acknowledge classical reasoning;
    every proof in §2–§9 is content with excluded middle and indefinite
    description.
*)
From mathcomp Require Import all_ssreflect.
From mathcomp.classical Require Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
