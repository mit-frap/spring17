(** * 6.887 Formal Reasoning About Programs, Spring 2017 - Pset 6 *)

Require Import Frap.

(* Authors: 
 * Joonwon Choi (joonwonc@csail.mit.edu), 
 * Adam Chlipala (adamc@csail.mit.edu)
 *)

(** * Syntax *)

Notation value := nat.

Inductive arith : Set :=
| Const : nat -> arith
| Var : var -> arith
| Eq : arith -> arith -> arith.

Notation pid := nat.

Inductive cmd :=
(** Normal commands *)
| Assign : var -> arith -> cmd
| If : arith -> list cmd (* then *) -> list cmd (* else *) -> cmd
| While : arith -> list cmd -> cmd
(** For message-passing *)
| SendMsg : pid (* to *) -> list arith -> cmd
| ReceiveMsg : list var -> cmd
(** End *)
| Return : arith -> cmd.

Notation pgm := (list cmd).
Notation pgms := (list (pid * pgm)).

(** Notations *)

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "==" := Eq (at level 75) : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75) : cmd_scope.
Notation "'if_' c 'then' t 'else' f" := (If c%arith t f) (at level 75) : cmd_scope.
Notation "'while' ( c ) cm" := (While c%arith cm) (at level 75) : cmd_scope.
Notation "'send' es 'to' i" := (SendMsg i es%arith) (at level 75) : cmd_scope.
Notation "'receive' xs" := (ReceiveMsg xs) (at level 75) : cmd_scope.
Notation "'ret' e" := (Return e%arith) (at level 75) : cmd_scope.

Delimit Scope cmd_scope with cmd.

(** * Problem 1: operational semantics *)

(* Put your semantics here! *)

(** * End of Problem 1 *)

(** * An implementation and the correctness proof: a very simple client and an echo server. *)

Section Echo.
  Variables (n: nat).

  (** Implementation *)
  
  Definition client_pid := 0.
  Definition server_pid := 1.

  Definition request_to_server := 1.
  Definition response_from_server := 2.

  Definition client := [
    "done" <- 0;
    while ("done" == 0) [
      send [Const request_to_server; Const n] to server_pid;
      receive ["code"; "res"];
      if_ "code" == response_from_server then [
        "done" <- 1
      ] else []
    ];
    ret "res"
  ]%cmd.

  Definition server := [
    while (1) [
      receive ["code"; "n"];
      if_ "code" == request_to_server then [
        send [Const response_from_server; Var "n"] to client_pid
      ] else []
    ];
    ret 0
  ]%cmd.

  Definition echo_client_server : pgms :=
    [(client_pid, client); (server_pid, server)].

  (** * Problem 2: correctness of the echo system *)

  (* Put your correctness statement and the proof here! *)

  (** * End of Problem 2 *)

End Echo.

