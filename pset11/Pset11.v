Require Import Frap Pset11Sig.

Set Implicit Arguments.


Theorem lookup_ok : forall x p,
  {{mtreep p}}
    lookup x p
  {{_ ~> mtreep p}}.
Proof.
Admitted.

Theorem insert_ok : forall x p,
  {{mtreep p}}
    insert x p
  {{_ ~> mtreep p}}.
Proof.
Admitted.
