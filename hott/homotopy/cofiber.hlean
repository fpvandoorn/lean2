(*
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

The Cofiber Type
*)
import hit.pushout function .susp types.unit

open eq pushout unit pointed is_trunc is_equiv susp unit equiv

Definition cofiber {A B : Type} (f : A -> B) . pushout f (fun (a : A) => ⋆)

namespace cofiber
  section
  parameters {A B : Type} (f : A -> B)

Definition cod : B -> cofiber f . inl
Definition base : cofiber f . inr ⋆

  parameter {f}
  protectedDefinition glue (a : A) : cofiber.cod f (f a) = cofiber.base f.
  pushout.glue a

  protectedDefinition rec {P : cofiber f -> Type} (Pcod : forall (b : B), P (cod b)) (Pbase : P base)
    (Pglue : forall (a : A), pathover P (Pcod (f a)) (glue a) Pbase) :
    (forall y, P y).
Proof.
    intro y, induction y, exact Pcod x, induction x, exact Pbase, exact Pglue x
Defined.

  protectedDefinition rec_on {P : cofiber f -> Type} (y : cofiber f)
    (Pcod : forall (b : B), P (cod b)) (Pbase : P base)
    (Pglue : forall (a : A), pathover P (Pcod (f a)) (glue a) Pbase) : P y.
  cofiber.rec Pcod Pbase Pglue y

  protectedDefinition rec_glue {P : cofiber f -> Type} (Pcod : forall (b : B), P (cod b)) (Pbase : P base)
    (Pglue : forall (a : A), pathover P (Pcod (f a)) (glue a) Pbase) (a : A)
    : apd (cofiber.rec Pcod Pbase Pglue) (cofiber.glue a) = Pglue a.
  !pushout.rec_glue

  protectedDefinition elim {P : Type} (Pcod : B -> P) (Pbase : P)
    (Pglue : forall (x : A), Pcod (f x) = Pbase) (y : cofiber f) : P.
  pushout.elim Pcod (fun u => Pbase) Pglue y

  protectedDefinition elim_on {P : Type} (y : cofiber f) (Pcod : B -> P) (Pbase : P)
    (Pglue : forall (x : A), Pcod (f x) = Pbase) : P.
  cofiber.elim Pcod Pbase Pglue y

  protectedDefinition elim_glue {P : Type} (Pcod : B -> P) (Pbase : P)
    (Pglue : forall (x : A), Pcod (f x) = Pbase) (a : A)
    : ap (cofiber.elim Pcod Pbase Pglue) (cofiber.glue a) = Pglue a.
  !pushout.elim_glue

Defined.

Defined. cofiber





(* pointed version *)

Definition pcofiber {A B : pType} (f : A ->* B) : pType.
pointed.MK (cofiber f) !cofiber.base

notation `ℂ` . pcofiber

namespace cofiber

  variables {A B : pType} (f : A ->* B)

Definition is_contr_cofiber_of_equiv [H : is_equiv f] : is_contr (cofiber f).
Proof.
    fapply is_contr.mk, exact cofiber.base f,
    intro a, induction a with b a,
    { exact !glue^-1 @ ap inl (right_inv f b) },
    { reflexivity },
    { apply eq_pathover_constant_left_id_right, apply move_top_of_left,
      refine _ @pv natural_square_tr cofiber.glue (left_inv f a) @vp (ap_pp _ _ _)stant,
      refine ap02 inl _ @ !ap_compose^-1, exact adj f a },
Defined.

Definition pcod (f : A ->* B) : B ->* pcofiber f.
  Build_pMap (cofiber.cod f) (ap inl (point_eq f)^-1 @ cofiber.glue (point _))

Definition pcod_pcompose (f : A ->* B) : pcod f o* f ==* pconst A (ℂ f).
Proof.
    fapply Build_pHomotopy,
    { intro a, exact cofiber.glue a },
    { exact !con_inv_cancel_left^-1 @ idp ◾ (!ap_inv^-1 ◾ idp) }
Defined.

Definition pcofiber_punit (A : pType) : pcofiber (pconst A punit) <~>* susp A.
Proof.
    fapply pequiv_of_pmap,
    { fapply Build_pMap, intro x, induction x, exact north, exact south, exact merid x,
      exact (merid (point _))^-1 },
    { esimp, fapply adjointify,
      { intro s, induction s, exact inl ⋆, exact inr ⋆, apply glue a },
      { intro s, induction s, do 2 reflexivity, esimp,
        apply eq_pathover, refine _ @hp !ap_id^-1, apply hdeg_square,
        refine !(ap_compose (pushout.elim _ _ _)) @ _,
        refine ap _ !elim_merid @ _, apply elim_glue },
      { intro c, induction c with u, induction u, reflexivity,
        reflexivity, esimp, apply eq_pathover, apply hdeg_square,
        refine _ @ !ap_id^-1, refine !(ap_compose (pushout.elim _ _ _)) @ _,
        refine ap02 _ !elim_glue @ _, apply elim_merid }},
Defined.

Defined. cofiber
