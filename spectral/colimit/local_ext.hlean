(*
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
*)

import hit.two_quotient .seq_colim

open eq prod sum two_quotient sigma function relation e_closure nat seq_colim

namespace localization
section quasi_local_extension

  universe variables u v w
  parameters {A : Type.{u}} {P : A -> Type.{v}} {Q : A -> Type.{w}} (F : forall a, P a -> Q a)
Definition is_local [class] (Y : Type) : Type.
  forall (a : A), is_equiv (fun g => g o F a : (Q a -> Y) -> (P a -> Y))



  section
  parameter (X : Type.{max u v w})
  local abbreviation Y . X + Σa, (P a -> X) \* Q a

  inductive qleR : Y -> Y -> Type.
  | J : forall {a : A} (f : P a -> X) (p : P a), qleR (inr ⟨a, (f, F a p)⟩) (inl (f p))
  | k : forall {a : A} (g : Q a -> X) (q : Q a), qleR (inl (g q)) (inr ⟨a, (g o F a, q)⟩)

  inductive qleQ : forall (y₁ y₂ : Y), e_closure qleR y₁ y₂ -> e_closure qleR y₁ y₂ -> Type.
  | K : forall {a : A} (g : Q a -> X) (p : P a), qleQ [qleR.k g (F a p)] [qleR.J (g o F a) p]^-1ʳ

Definition one_step_localization : Type . two_quotient qleR qleQ
Definition incl : X -> one_step_localization . incl0 _ _ o inl

Defined.
  variables (X : Type.{max u v w}) {Z : Type}

Definition n_step_localization : ℕ -> Type.
  nat.rec X (fun n Y => localization.one_step_localization F Y)

Definition incln (n : ℕ) :
  n_step_localization X n -> n_step_localization X (succ n).
  localization.incl F (n_step_localization X n)

Definition localization : Type . seq_colim (incln X)
Definition incll : X -> localization X . ι' _ 0

  protectedDefinition rec {P : localization X -> Type} [forall z, is_local (P z)]
  (H : forall x, P (incll X x)) (z : localization X) : P z.
Proof.
  exact sorry
Defined.

Definition extend {Y Z : Type} (f : Y -> Z) [is_local Z] (x : one_step_localization Y) : Z.
Proof.
  induction x,
  { induction a,
  { exact f a},
  { induction a with a v, induction v with f q, exact sorry}},
  { exact sorry},
  { exact sorry}
Defined.

  protectedDefinition elim {Y : Type} [is_local Y]
  (H : X -> Y) (z : localization X) : Y.
Proof.
  induction z with n x n x,
  { induction n with n IH,
  { exact H x},
  induction x,
  { induction a,
  { exact IH a},
  { induction a with a v, induction v with f q, exact sorry}},
  { exact sorry},
  exact sorry},
  exact sorry
Defined.


Defined. quasi_local_extension
Defined. localization
