(*
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
*)

prelude
import .equiv
open eq equiv is_equiv

axiom univalence (A B : Type) : is_equiv (@equiv_of_eq A B)



(* This is the version of univalence axiom we will probably use most often *)
Definition ua {A B : Type} : A <~> B -> A = B.
equiv_of_eq^-1

Definition eq_equiv_equiv (A B : Type) : (A = B) <~> (A <~> B).
equiv.mk equiv_of_eq _

Definition equiv_of_eq_ua {A B : Type} (f : A <~> B) : equiv_of_eq (ua f) = f.
right_inv equiv_of_eq f

Definition cast_ua_fn {A B : Type} (f : A <~> B) : cast (ua f) = f.
ap to_fun (equiv_of_eq_ua f)

Definition cast_ua {A B : Type} (f : A <~> B) (a : A) : cast (ua f) a = f a.
ap10 (cast_ua_fn f) a

Definition cast_ua_inv_fn {A B : Type} (f : A <~> B) : cast (ua f)^-1 = to_inv f.
ap to_inv (equiv_of_eq_ua f)

Definition cast_ua_inv {A B : Type} (f : A <~> B) (b : B) : cast (ua f)^-1 b = to_inv f b.
ap10 (cast_ua_inv_fn f) b

Definition ua_equiv_of_eq {A B : Type} (p : A = B) : ua (equiv_of_eq p) = p.
left_inv equiv_of_eq p

Definition eq_of_equiv_lift {A B : Type} (f : A <~> B) : A = lift B.
ua (f @e !equiv_lift)

namespace equiv

  (* One consequence of UA is that we can transport along equivalencies of types *)
  (* We can use this for calculation evironments *)
  protectedDefinition transport_of_equiv [subst] (P : Type -> Type) {A B : Type} (H : A <~> B)
    : P A -> P B.
  eq.transport P (ua H)

  (* we can "recurse" on equivalences, by replacing them by (equiv_of_eq _) *)
Definition rec_on_ua [recursor] {A B : Type} {P : A <~> B -> Type}
    (f : A <~> B) (H : forall (q : A = B), P (equiv_of_eq q)) : P f.
  right_inv equiv_of_eq f # H (ua f)

  (* a variant where we immediately recurse on the equality in the new goal *)
Definition rec_on_ua_idp [recursor] {A : Type} {P : forall {B}, A <~> B -> Type} {B : Type}
    (f : A <~> B) (H : P equiv.rfl) : P f.
  rec_on_ua f (fun q => eq.rec_on q H)

  (* a variant where (equiv_of_eq (ua f)) will be replaced by f in the new goal *)
Definition rec_on_ua' {A B : Type} {P : A <~> B -> A = B -> Type}
    (f : A <~> B) (H : forall (q : A = B), P (equiv_of_eq q) q) : P f (ua f).
  right_inv equiv_of_eq f # H (ua f)

  (* a variant where we do both *)
Definition rec_on_ua_idp' {A : Type} {P : forall {B}, A <~> B -> A = B -> Type} {B : Type}
    (f : A <~> B) (H : P equiv.rfl idp) : P f (ua f).
  rec_on_ua' f (fun q => eq.rec_on q H)

Definition ua_refl (A : Type) : ua erfl = idpath A.
  eq_of_fn_eq_fn !eq_equiv_equiv (right_inv !eq_equiv_equiv erfl)

Definition ua_symm {A B : Type} (f : A <~> B) : ua f^-1ᵉ = (ua f)^-1.
Proof.
    apply rec_on_ua_idp f,
    refine !ua_refl @ inverse2 !ua_refl^-1
Defined.

Definition ua_trans {A B C : Type} (f : A <~> B) (g : B <~> C) : ua (f @e g) = ua f @ ua g.
Proof.
    apply rec_on_ua_idp g, apply rec_on_ua_idp f,
    refine !ua_refl @ concat2 !ua_refl^-1 !ua_refl^-1
Defined.


Defined. equiv
