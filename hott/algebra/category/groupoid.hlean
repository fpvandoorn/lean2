(*
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
*)

import .iso algebra.bundled

open eq is_trunc iso category algebra nat unit

namespace category

  structure groupoid [class] (ob : Type) extends parent : precategory ob.
  mk' :: (all_iso : forall (a b : ob) (f : hom a b), @is_iso ob parent a b f)

  abbreviation all_iso . @groupoid.all_iso
  attribute groupoid.all_iso [instance] [priority 3000]
  attribute groupoid.to_precategory [unfold 2]
Definition groupoid.mk {ob : Type} (C : precategory ob)
    (H : forall (a b : ob) (f : a ⟶ b), is_iso f) : groupoid ob.
  precategory.rec_on C groupoid.mk' H

Definition groupoid_of_group.{l} (A : Type.{l}) [G : group A] :
    groupoid.{0 l} unit.
Proof.
    fapply groupoid.mk; fapply precategory.mk: intros,
      { exact A},
      { exact _},
      { exact a_2 * a_1},
      { exact 1},
      { apply mul.assoc},
      { apply mul_one},
      { apply one_mul},
      { esimp [precategory.mk],
        fapply is_iso.mk,
        { exact f^-1},
        { apply mul.right_inv},
        { apply mul.left_inv}},
Defined.

Definition hom_group {A : Type} [G : groupoid A] (a : A) : group (hom a a).
Proof.
    fapply group.mk,
      apply is_set_hom,
      intro f g, apply (comp f g),
      intros f g h, apply (assoc f g h)^-1,
      apply (ID a),
      intro f, apply id_left,
      intro f, apply id_right,
      intro f, exact (iso.inverse f),
      intro f, exact (iso.left_inverse f),
Defined.

Definition group_of_is_contr_groupoid {ob : Type} [H : is_contr ob]
    [G : groupoid ob] : group (hom (center ob) (center ob)) . !hom_group
Definition group_of_groupoid_unit [G : groupoid unit] : group (hom ⋆ ⋆) . !hom_group

  (* Bundled version of categories *)
  (* we don't use Groupoid.carrier explicitly, but rather use Groupoid.carrier (to_Precategory C) *)
  structure Groupoid : Type.
    (carrier : Type)
    (struct : groupoid carrier)

  attribute Groupoid.struct [instance] [coercion]

Definition Groupoid.to_Precategory [coercion] (C : Groupoid)
    : Precategory.
  Precategory.mk (Groupoid.carrier C) _

  attribute Groupoid._trans_of_to_Precategory_1 [unfold 1]

Definition groupoid.Mk . Groupoid.mk
Definition groupoid.MK (C : Precategory)
    (H : forall (a b : C) (f : a ⟶ b), is_iso f) : Groupoid.
  Groupoid.mk C (groupoid.mk C H)

Definition Groupoid.eta (C : Groupoid) : Groupoid.mk C C = C.
  Groupoid.rec (fun ob c => idp) C

Definition Groupoid_of_Group (G : Group) : Groupoid.
  Groupoid.mk unit (groupoid_of_group G)

Defined. category
