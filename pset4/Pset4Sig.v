(** * 6.887 Formal Reasoning About Programs, Spring 2017 - Pset 4 *)

Require Import Frap.

Set Implicit Arguments.


(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)


(* A copy of the parallel transition-system combinator from TransitionSystem.v *)

Record threaded_state shared private := {
  Shared : shared;
  Private : private
}.

Inductive parallel1 shared private1 private2
  (init1 : threaded_state shared private1 -> Prop)
  (init2 : threaded_state shared private2 -> Prop)
  : threaded_state shared (private1 * private2) -> Prop :=
| Pinit : forall sh pr1 pr2,
  init1 {| Shared := sh; Private := pr1 |}
  -> init2 {| Shared := sh; Private := pr2 |}
  -> parallel1 init1 init2 {| Shared := sh; Private := (pr1, pr2) |}.

Inductive parallel2 shared private1 private2
          (step1 : threaded_state shared private1 -> threaded_state shared private1 -> Prop)
          (step2 : threaded_state shared private2 -> threaded_state shared private2 -> Prop)
          : threaded_state shared (private1 * private2)
            -> threaded_state shared (private1 * private2) -> Prop :=
| Pstep1 : forall sh pr1 pr2 sh' pr1',
  (* First thread gets to run. *)
  step1 {| Shared := sh; Private := pr1 |} {| Shared := sh'; Private := pr1' |}
  -> parallel2 step1 step2 {| Shared := sh; Private := (pr1, pr2) |}
               {| Shared := sh'; Private := (pr1', pr2) |}
| Pstep2 : forall sh pr1 pr2 sh' pr2',
  (* Second thread gets to run. *)
  step2 {| Shared := sh; Private := pr2 |} {| Shared := sh'; Private := pr2' |}
  -> parallel2 step1 step2 {| Shared := sh; Private := (pr1, pr2) |}
               {| Shared := sh'; Private := (pr1, pr2') |}.

Definition parallel shared private1 private2
           (sys1 : trsys (threaded_state shared private1))
           (sys2 : trsys (threaded_state shared private2)) := {|
  Initial := parallel1 sys1.(Initial) sys2.(Initial);
  Step := parallel2 sys1.(Step) sys2.(Step)
|}.


(* Now, we come to the main problem to be solved: prove the correctness of a
 * famous locking algorithm, applied to the particular example of incrementing a
 * counter from the lecture code.  Instead of assuming that a correct
 * implementation of locking is provided to us, we provide our own, on top of
 * basic atomic read/write operations on shared variables!
 * Specifically, we use Peterson's Algorithm, which you can read about here:
 *   https://en.wikipedia.org/wiki/Peterson%27s_algorithm *)

(** Instantiated to our setting, it's equivalent to this code.

  bool flag[2] = {false, false};
  bool turn = false;
  int global = 0;

  oneThread(me, other) {
    int local;

    flag[me] = true;
    turn = other;
    while (flag[other] && turn == other);
    local = global;
    global = local + 1;
    flag[me] = false;
  }

  The idea is that we run "oneThread(0, 1)" in parallel with "oneThread(1, 0)".
  After both threads finish, "global" had better be holding the value 2.
*)

(* We formalize local states with this type, standing for the different points
 * before, between, and after the lines of code, in order.  Note that, as with
 * the example from lecture, only the [Write] state needs to store the value of
 * variable "local". *)
Inductive increment_program :=
| SetFlag : increment_program
| SetTurn : increment_program
| ReadFlag : increment_program
| ReadTurn : increment_program
| Read : increment_program
| Write : nat -> increment_program
| UnsetFlag : increment_program
| Done : increment_program.

(* Record of global variables *)
Record inc_state := {
  Flag1 : bool;
  Flag2 : bool;
  (* The two cells of the "flag" array, represented as separate variables *)
  Turn : bool;
  (* Global variable "turn", representing with "false" for 0 and "true" for 1 *)
  Global : nat
  (* Global variable "global", represented more directly *)
}.

Definition increment_state := threaded_state inc_state increment_program.

(* The next two relations translate the single-thread code in a tedious way. *)

Inductive increment_init : increment_state -> Prop :=
| IncInit :
  increment_init {| Shared := {| Flag1 := false; Flag2 := false; Turn := false; Global := O |};
                    Private := SetFlag |}.

Inductive increment_step : bool (* This Boolean is set iff parameter "me" would
                                 * be 1. *)
                           -> increment_state -> increment_state -> Prop :=
| IncSetFlag1 : forall fl1 fl2 tu g,
  increment_step false
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := SetFlag |}
                 {| Shared := {| Flag1 := true; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := SetTurn |}
| IncSetFlag2 : forall fl1 fl2 tu g,
  increment_step true
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := SetFlag |}
                 {| Shared := {| Flag1 := fl1; Flag2 := true; Turn := tu; Global := g |};
                    Private := SetTurn |}
| IncSetTurn : forall am2 fl1 fl2 tu g,
  increment_step am2
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := SetTurn |}
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := negb am2; Global := g |};
                    Private := ReadFlag |}
| IncReadFlag1True : forall fl1 fl2 tu g,
  fl2 = true
  -> increment_step false
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := ReadFlag |}
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := ReadTurn |}
| IncReadFlag1False : forall fl1 fl2 tu g,
  fl2 = false
  -> increment_step false
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := ReadFlag |}
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := Read |}
| IncReadFlag2True : forall fl1 fl2 tu g,
  fl1 = true
  -> increment_step true
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := ReadFlag |}
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := ReadTurn |}
| IncReadFlag2False : forall fl1 fl2 tu g,
  fl1 = false
  -> increment_step true
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := ReadFlag |}
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := Read |}
| IncReadTurnTrue : forall am2 fl1 fl2 g,
  increment_step am2
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := negb am2; Global := g |};
                    Private := ReadTurn |}
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := negb am2; Global := g |};
                    Private := ReadFlag |}
| IncReadTurnFalse : forall am2 fl1 fl2 g,
  increment_step am2
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := am2; Global := g |};
                    Private := ReadTurn |}
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := am2; Global := g |};
                    Private := Read |}
| IncRead : forall am2 fl1 fl2 tu g,
  increment_step am2
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := Read |}
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := Write g |}
| IncWrite : forall am2 fl1 fl2 tu g v,
  increment_step am2
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := Write v |}
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := S v |};
                    Private := UnsetFlag |}
| IncUnsetFlag1 : forall fl1 fl2 tu g,
  increment_step false
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := UnsetFlag |}
                 {| Shared := {| Flag1 := false; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := Done |}
| IncUnsetFlag2 : forall fl1 fl2 tu g,
  increment_step true
                 {| Shared := {| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |};
                    Private := UnsetFlag |}
                 {| Shared := {| Flag1 := fl1; Flag2 := false; Turn := tu; Global := g |};
                    Private := Done |}.

Definition increment_sys am2 := {|
  Initial := increment_init;
  Step := increment_step am2
|}.

Definition increment2_sys := parallel (increment_sys false) (increment_sys true).

(* The natural correctness condition, looking nearly the same as for the example
 * from lecture *)
Definition increment2_correct (s : threaded_state inc_state (increment_program * increment_program)) :=
  s.(Private) = (Done, Done)
  -> s.(Shared).(Global) = 2.

Module Type S.
  Axiom increment2_ok :
    invariantFor increment2_sys increment2_correct.
End S.
