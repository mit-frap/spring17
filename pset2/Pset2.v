Require Import Frap Pset2Sig.
Require Import OrdersFacts.

(* For your convenience, we beforehand provide some useful facts about orders.
 * You can skim through the list of theorems by using "Print," or visiting 
 * this page:
 * https://coq.inria.fr/library/Coq.Structures.OrdersFacts.html
 *)
Include (OrderedTypeFacts Pset2Sig).
Include (OrderedTypeTest Pset2Sig).
(* Print OrderedTypeFacts. *)
(* Print OrderedTypeTest. *)

(* Our proof also uses the following facts that have been included above from libraries. *)
Check eq_lt.
Check eq_sym.
Check lt_eq.
Check lt_not_eq.
Check lt_trans.
Check compare_refl.
Check compare_lt_iff. (* Note that this one can be used with [apply], despite the fact that it
                       * includes an "if and only if" ([<->]) where other theorems use simple
                       * implication ([->]). *)
Check compare_gt_iff.
Check compare_eq_iff.

Theorem insert_member: forall tr n, BST tr -> member n (insert n tr) = true.
Proof.
Admitted.

Theorem insert_ok: forall tr n, BST tr -> BST (insert n tr).
Proof.
Admitted.

Theorem delete_ok: forall tr n, BST tr -> BST (delete n tr).
Proof.
Admitted.

(* OPTIONAL PART! *)
(*Theorem delete_member: forall tr n, BST tr -> member n (delete n tr) = false.
Proof.
Admitted.*)
