(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Category of sets
*)

import ..functor.basic ..category types.equiv types.lift

open eq category equiv iso is_equiv is_trunc function sigma

namespace category

Definition precategory_Set.{u} : precategory Set.{u}.
  precategory.mk (fun x y : Set => x -> y)
                 (fun x y z g f a => g (f a))
                 (fun x a => a)
                 (fun x y z w h g f => eq_of_homotopy (fun a => idp))
                 (fun x y f => eq_of_homotopy (fun a => idp))
                 (fun x y f => eq_of_homotopy (fun a => idp))

Definition Precategory_Set : Precategory.
  Precategory.mk Set precategory_Set

  abbreviation set . Precategory_Set

  namespace set
    local attribute is_equiv_subtype_eq [instance]
Definition iso_of_equiv {A B : set} (f : A <~> B) : A ≅ B.
    iso.MK (to_fun f)
           (to_inv f)
           (eq_of_homotopy (left_inv (to_fun f)))
           (eq_of_homotopy (right_inv (to_fun f)))

Definition equiv_of_iso {A B : set} (f : A ≅ B) : A <~> B.
    begin
      apply equiv.MK (to_hom f) (iso.to_inv f),
        exact ap10 (to_right_inverse f),
        exact ap10 (to_left_inverse f)
    end

Definition is_equiv_iso_of_equiv (A B : set)
      : is_equiv (@iso_of_equiv A B).
    adjointify _ (fun f => equiv_of_iso f)
                 (fun f => proof iso_eq idp qed)
                 (fun f => equiv_eq' idp)

    local attribute is_equiv_iso_of_equiv [instance]

Definition iso_of_eq_eq_compose (A B : Set) : @iso_of_eq _ _ A B ~
      @iso_of_equiv A B o @equiv_of_eq A B o subtype_eq_inv _ _ o
      @ap _ _ (to_fun (trunctype.sigma_char 0)) A B.
    fun p => eq.rec_on p idp

Definition equiv_equiv_iso (A B : set) : (A <~> B) <~> (A ≅ B).
    equiv.MK (fun f => iso_of_equiv f)
             (fun f => proof equiv.MK (to_hom f)
                           (iso.to_inv f)
                           (ap10 (to_right_inverse f))
                           (ap10 (to_left_inverse  f)) qed)
             (fun f => proof iso_eq idp qed)
             (fun f => proof equiv_eq' idp qed)

Definition equiv_eq_iso (A B : set) : (A <~> B) = (A ≅ B).
    ua !equiv_equiv_iso

Definition is_univalent_Set (A B : set) : is_equiv (iso_of_eq : A = B -> A ≅ B).
    have H₁ : is_equiv (@iso_of_equiv A B o @equiv_of_eq A B o subtype_eq_inv _ _ o
              @ap _ _ (to_fun (trunctype.sigma_char 0)) A B) => from
      @is_equiv_compose _ _ _ _ _
      (@is_equiv_compose _ _ _ _ _
         (@is_equiv_compose _ _ _ _ _
           _
           (@is_equiv_subtype_eq_inv _ _ _ _ _))
         !univalence)
       !is_equiv_iso_of_equiv,
    is_equiv.homotopy_closed _ (iso_of_eq_eq_compose A B)^-1ʰᵗʸ

Defined. set

Definition category_Set [instance] : category Set.
  category.mk precategory_Set set.is_univalent_Set

Definition Category_Set : Category.
  Category.mk Set category_Set

  abbreviation cset . Category_Set

  open functor lift
Definition functor_lift.{u v} : set.{u} ⇒ set.{max u v}.
  functor.mk tlift
             (fun a b => lift_functor)
             (fun a => eq_of_homotopy (fun x => by induction x; reflexivity))
             (fun a b c g f => eq_of_homotopy (fun x => by induction x; reflexivity))


Defined. category
