(** * 6.887 Formal Reasoning About Programs, Spring 2017 - Pset 7 *)

Require Import Frap Pset7Sig.

Theorem validator_ok:
  forall v s t, validator s t = true -> (v, s) =| (v, t).
Proof.
Admitted.