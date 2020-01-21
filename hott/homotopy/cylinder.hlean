(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of mapping cylinders
*)

import hit.quotient types.fiber

open quotient eq sum equiv fiber

namespace cylinder
section

  parameters {A B : Type} (f : A -> B)

  local abbreviation C . B + A
  inductive cylinder_rel : C -> C -> Type.
  | Rmk : forall (a : A), cylinder_rel (inl (f a)) (inr a)
  open cylinder_rel
  local abbreviation R . cylinder_rel

Definition cylinder . quotient cylinder_rel (* TODO: define this in root namespace *)

  parameter {f}
Definition base (b : B) : cylinder.
  class_of R (inl b)

Definition top (a : A) : cylinder.
  class_of R (inr a)

Definition seg (a : A) : base (f a) = top a.
  eq_of_rel cylinder_rel (Rmk f a)

  protectedDefinition rec {P : cylinder -> Type}
    (Pbase : forall (b : B), P (base b)) (Ptop : forall (a : A), P (top a))
    (Pseg : forall (a : A), Pbase (f a) =[seg a] Ptop a) (x : cylinder) : P x.
Proof.
    induction x,
    { cases a,
        apply Pbase,
        apply Ptop},
    { cases H, apply Pseg}
Defined.

  protectedDefinition rec_on {P : cylinder -> Type} (x : cylinder)
    (Pbase : forall (b : B), P (base b)) (Ptop  : forall (a : A), P (top a))
    (Pseg  : forall (a : A), Pbase (f a) =[seg a] Ptop a) : P x.
  rec Pbase Ptop Pseg x

Definition rec_seg {P : cylinder -> Type}
    (Pbase : forall (b : B), P (base b)) (Ptop : forall (a : A), P (top a))
    (Pseg : forall (a : A), Pbase (f a) =[seg a] Ptop a)
      (a : A) : apd (rec Pbase Ptop Pseg) (seg a) = Pseg a.
  !rec_eq_of_rel

  protectedDefinition elim {P : Type} (Pbase : B -> P) (Ptop : A -> P)
    (Pseg : forall (a : A), Pbase (f a) = Ptop a) (x : cylinder) : P.
  rec Pbase Ptop (fun a => pathover_of_eq _ (Pseg a)) x

  protectedDefinition elim_on {P : Type} (x : cylinder) (Pbase : B -> P) (Ptop : A -> P)
    (Pseg : forall (a : A), Pbase (f a) = Ptop a) : P.
  elim Pbase Ptop Pseg x

Definition elim_seg {P : Type} (Pbase : B -> P) (Ptop : A -> P)
    (Pseg : forall (a : A), Pbase (f a) = Ptop a)
    (a : A) : ap (elim Pbase Ptop Pseg) (seg a) = Pseg a.
Proof.
    apply eq_of_fn_eq_fn_inv !(pathover_constant (seg a)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim,rec_seg],
Defined.

  protectedDefinition elim_type (Pbase : B -> Type) (Ptop : A -> Type)
    (Pseg : forall (a : A), Pbase (f a) <~> Ptop a) (x : cylinder) : Type.
  elim Pbase Ptop (fun a => ua (Pseg a)) x

  protectedDefinition elim_type_on (x : cylinder) (Pbase : B -> Type) (Ptop : A -> Type)
    (Pseg : forall (a : A), Pbase (f a) <~> Ptop a) : Type.
  elim_type Pbase Ptop Pseg x

Definition elim_type_seg (Pbase : B -> Type) (Ptop : A -> Type)
    (Pseg : forall (a : A), Pbase (f a) <~> Ptop a)
    (a : A) : transport (elim_type Pbase Ptop Pseg) (seg a) = Pseg a.
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_seg];apply cast_ua_fn

Defined.

Defined. cylinder







namespace cylinder
  open sigma sigma.ops
  variables {A B : Type} (f : A -> B)

  (* cylinder as a dependent family *)
Definition pr1 : cylinder f -> B.
  cylinder.elim id f (fun a => idp)

Definition fcylinder : B -> Type . fiber (pr1 f)

Definition cylinder_equiv_sigma_fcylinder : cylinder f <~> Σb, fcylinder f b.
  !sigma_fiber_equiv^-1ᵉ

  variable {f}
Definition fbase (b : B) : fcylinder f b.
  fiber.mk (base b) idp

Definition ftop (a : A) : fcylinder f (f a).
  fiber.mk (top a) idp

Definition fseg (a : A) : fbase (f a) = ftop a.
  fiber_eq (seg a) !elim_seg^-1

(* TODO: define the induction principle for "fcylinder" *)
(*   set_option pp.notation false *)
(*   (* The induction principle for the dependent mapping cylinder (TODO) *) *)
(*   protectedDefinition frec {P : forall (b), fcylinder f b -> Type} *)
(*     (Pbase : forall (b : B), P _ (fbase b)) (Ptop : forall (a : A), P _ (ftop a)) *)
(*     (Pseg : forall (a : A), Pbase (f a) =[fseg a] Ptop a) {b : B} (x : fcylinder f b) : P _ x . *)
(*   begin *)
(*     cases x with x p, induction p, *)
(*     induction x: esimp, *)
(*     { apply Pbase}, *)
(*     { apply Ptop}, *)
(*     { esimp, --fapply fiber_pathover, *)
(*              --refine pathover_of_pathover_ap P (fun x => fiber.mk x idp), *)

(* exact sorry} *)
(*   end *)

(*Definition frec_fseg {P : forall (b), fcylinder f b -> Type} *)
(*     (Pbase : forall (b : B), P _ (fbase b)) (Ptop : forall (a : A), P _ (ftop a)) *)
(*     (Pseg : forall (a : A), Pbase (f a) =[fseg a] Ptop a) (a : A) *)
(*     : apd (cylinder.frec Pbase Ptop Pseg) (fseg a) = Pseg a . *)
(*   sorry *)


Defined. cylinder
