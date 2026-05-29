(**md**************************************************************************)
(** * Deprecated shim: named-syntax PPL is now in [theories/programs/ppl.v]

    This file is a deprecated SHIM that re-exports the named-variable
    PPL of [theories/programs/ppl.v].  It is scheduled for removal in
    Step 5 of the PPL refactor (see commit log).  Downstream files
    should import [Icones.programs.ppl] directly. *)

Require Export Icones.programs.ppl.
