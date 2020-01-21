(*
Copyright (c) 2015 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz
*)
import types.trunc homotopy.sphere hit.pushout

open eq is_trunc is_equiv nat equiv trunc prod pushout sigma unit pointed

(* where should this be? *)
Definition family : Type . ΣX, X -> Type

namespace cellcomplex

  (*
    define by recursion on ℕ
    both the type of fdccs of dimension n
    and the realization map fdcc n -> Type

    in other words, we define a function
    fdcc : ℕ -> family

    an alternative to the approach here (perhaps necessary) is to
    define relative cell complexes relative to a type A, and then use
    spherical indexing, so a -1-dimensional relative cell complex is
    just star : unit with realization A
  *)

Definition fdcc_family : ℕ -> family.
  nat.rec
    (* a zero-dimensional cell complex is just an set *)
    (* with realization the identity map *)
    ⟨Set , fun A => trunctype.carrier A⟩
    (fun n fdcc_family_n => (* sigma.rec (fun fdcc_n realize_n => *)
      (* a (succ n)-dimensional cell complex is a triple of
         an n-dimensional cell complex X, an set of (succ n)-cells A,
         and an attaching map f : A \* sphere n -> |X| *)
      ⟨Σ X : pr1 fdcc_family_n , Σ A : Set, A \* sphere n -> pr2 fdcc_family_n X ,
      (* the realization of such is the pushout of f with
         canonical map A \* sphere n -> unit *)
       sigma.rec (fun X  => sigma.rec (fun A f => pushout (fun x  => star) f))
      ⟩)

Definition fdcc (n : ℕ) : Type . pr1 (fdcc_family n)

Definition cell : forall n, fdcc n -> Set.
  nat.cases (fun A => A) (fun n T => pr1 (pr2 T))

Defined. cellcomplex
