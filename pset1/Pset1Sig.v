(** * 6.887 Formal Reasoning About Programs, Spring 2017 - Pset 1 *)

Require Import Frap.
(* If this import command doesn't work, something may be wrong with the copy
 * of the FRAP book source that has been included as a Git submodule.
 * Running `git submodule init' or `git submodule update' in the repository
 * base directory might help.  However, it's also necessary to build the
 * book library, like so (starting from the base of this repository):
 * <<
     make -C frap lib
   >>
 * See below for installing Coq, which is a prerequisite for the above to work.
 *)

(* Authors:
 * Peng Wang (wangpeng@csail.mit.edu), 
 * Adam Chlipala (adamc@csail.mit.edu),
 * Joonwon Choi (joonwonc@csail.mit.edu)
 *)

(* This lightweight pset is meant to force you to get started installing Coq
 * and finding bugs in our homework-submission system!  *ahem*  We meant
 * "learning to use our homework-submission system." ;-) *)

(*
 * All the psets we provide should be compatible with several Coq versions,
 * including 8.4, 8.5, and 8.6.  If you haven't installed Coq before, we
 * encourage you to install the up-to-date version, which is 8.6, though you
 * may also find it more convenient to install a package from your
 * operating system.  For instance:
 * - Coq has been included with Ubuntu <https://www.ubuntu.com/> for a while,
 *   and the last two long-term-stable releases include new enough Coq versions.
 *   Just run `apt-get install coq'.
 * - Mac Homebrew <http://brew.sh/> also includes a new enough version.
 *   Just run `brew install coq'.
 *
 * To install from source, see the official download page:
 *   https://coq.inria.fr/download
 *
 * It will also be *essential* to install a UI for editing Coq proofs!
 * The course staff use and recommend Proof General <https://proofgeneral.github.io/>,
 * which is a mode for the Emacs IDE.  The Proof General project page includes
 * instructions for installing from GitHub.  Some older versions, say from OS
 * packages, may work fine for this class, too.  By the way, one MIT student is a
 * current maintainer of Proof General, and some other MIT people have contributed
 * code to it recently, so you will get especially expert help if you choose this UI!
 *
 * However, there is a standalone Coq IDE called, fittingly, CoqIDE, which
 * ships with Coq itself.  It has a less steep learning curve, though many of us
 * believe that Proof General supports more productive coding, after spending some
 * practice time.
 *
 * We will have special office hours the day after this assignment goes out,
 * to help everyone get these packages set up.
 *
 * Now, on to the actual assignment, once you have Coq and a UI installed!
 *)

(* The Coq standard library contains a definition of a type of lists, a common
 * concept in functional programming.  More mainstream languages might call such
 * a thing an "immutable, singly linked list."
 *
 * Here's the type definition, which is effectively included automatically,
 * by default, in any Coq file.
 * <<
     Inductive list A :=
       nil
     | cons (hd : A) (tl : list A).
   >>
 *
 * [A] is a type parameter.  (Note that, following Coq's code-documentation
 * conventions, we put square brackets around bits of code within comments,
 * and we use double-angle brackets to set off larger code excerpts.)
 * This list type is a lot like the syntax-tree types we saw in class;
 * the only new wrinkle is the polymorphic type parameter [A], which is
 * related to *generics* in OO languages.  (We'll study this feature more
 * carefully in the next lecture.)
 *
 * We can also define some useful operations on lists.
 * A basic one is length.
 * <<
    Fixpoint length {A} (xs : list A) : nat :=
      match xs with
        | nil => 0
        | cons _ xs' => 1 + length xs'
      end.
   >>
 * Note the use of the natural-number type [nat].
 * The curly braces in type argument [{A}] tell Coq to infer this type argument
 * when [length] is called, which by the way is the default behavior for all
 * type arguments in Haskell and OCaml.
 * Another function is concatenation of lists, defined using an infix operator
 * [::] for [cons].
 * <<
    Fixpoint app {A} (l : list A) (m : list A) : list A :=
      match l with
       | nil => m
       | a :: l1 => a :: app l1 m
      end.
   >>
 * Finally, we'll also work with list reversal, using [++] as an infix operator
 * for [app].
 * <<
    Fixpoint rev {A} (l : list A) : list A :=
      match l with
        | nil => nil
        | x :: l' => rev l' ++ (x :: nil)
      end.
   >>
 *)

(* Here's an example proof with lists, using a list shorthand notation. *)
Theorem an_important_theorem : length [1; 2; 3] = 3.
Proof.
  simplify.
  equality.
Qed.


(* OK, enough warmup.  Your job is to define a module implementing the following
 * signature.  We ask you to implement a file Pset1.v, where the skeleton is 
 * already given, such that it can be checked against this signature by 
 * successfully processing a third file (Pset1Check.v) with a command like so:
 * <<
    Require Pset1Sig Pset1.

    Module M : Pset1Sig.S := Pset1.
   >>
 * You'll need to build your module first, which the default target of our
 * handy Makefile does for you automatically.  Note that the _CoqProject
 * file included here is also important for making compilation and
 * interactive editing work.  Your Pset1.v file is what you upload to the course
 * web site to get credit for doing the assignment.
 *)

(* Finally, here's the actual signature to implement. *)
Module Type S.
  Axiom another_important_theorem : length [1; 2; 3] = 1 + length [4; 5].

  Axiom length_concat : forall A (xs ys : list A),
      length (xs ++ ys) = length xs + length ys.
  (* Hint: want induction for this one! *)

  Axiom length_rev : forall A (xs : list A),
      length xs = length (rev xs).
  (* Hint: appeal to [length_concat] somewhere! *)
End S.
