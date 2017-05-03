Require Import Frap Pset12Sig.


Theorem deadlock_freedom :
  forall h p,
    Forall (fun c => goodCitizen {} c {}) p ->
    invariantFor (trsys_of h {} p) (fun h_l_p =>
                                      let '(_, _, p') := h_l_p in
                                      Forall finished p'
                                      \/ exists h_l_p', step h_l_p h_l_p').
Proof.
  (* To begin with, we weaken the invariant to the one proved in Pset11Sig. *)
  simplify.
  eapply invariant_weaken.
  eauto using a_useful_invariant.

  (* What's left is to prove that that invariant implies deadlock-freedom. *)
  first_order.
  cases s.
  cases p0.
  invert H0.

  (* We don't actually need to use the [disjointLocks] property.  It was only
   * important in strengthening the induction to prove that other invariant.
   * Also, the original hypothesis won't be needed anymore.*)
  clear H H6.
Admitted.
