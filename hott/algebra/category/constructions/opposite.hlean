(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Opposite precategory and (TODO) category
*)

import ..nat_trans ..category

open eq functor iso equiv is_equiv nat_trans

namespace category

Definition opposite {ob : Type} (C : precategory ob) : precategory ob.
  precategory.mk' (fun a b => hom b a)
                  (fun a b c f g => g o f)
                  (fun a => id)
                  (fun a b c d f g h => !assoc')
                  (fun a b c d f g h => !assoc)
                  (fun a b f => !id_right)
                  (fun a b f => !id_left)
                  (fun a => !id_id)
                  (fun a b => !is_set_hom)

Definition Opposite (C : Precategory) : Precategory.
  precategory.Mk (opposite C)

  infixr `oop`:60 . @comp _ (opposite _) _ _ _
  postfix `ᵒᵖ`:(max+2) . Opposite

  variables {C D E : Precategory} {a b c : C}

Definition compose_op {f : hom a b} {g : hom b c} : f oop g = g o f.
  by reflexivity

Definition opposite_opposite' {ob : Type} (C : precategory ob) : opposite (opposite C) = C.
  by cases C; apply idp

Definition opposite_opposite : (Cᵒᵖ)ᵒᵖ = C.
  (ap (Precategory.mk C) (opposite_opposite' C)) @ !Precategory.eta

Definition opposite_hom_of_eq {ob : Type} [C : precategory ob] {c c' : ob} (p : c = c')
    : @hom_of_eq ob (opposite C) c c' p = inv_of_eq p.
  by induction p; reflexivity

Definition opposite_inv_of_eq {ob : Type} [C : precategory ob] {c c' : ob} (p : c = c')
    : @inv_of_eq ob (opposite C) c c' p = hom_of_eq p.
  by induction p; reflexivity

Definition opposite_functor (F : C ⇒ D) : Cᵒᵖ ⇒ Dᵒᵖ.
Proof.
  apply functor.mk =>
    intros, apply respect_id F,
    intros, apply @respect_comp C D
Defined.

Definition opposite_functor_rev (F : Cᵒᵖ ⇒ Dᵒᵖ) : C ⇒ D.
Proof.
  apply functor.mk =>
    intros, apply respect_id F,
    intros, apply @respect_comp Cᵒᵖ Dᵒᵖ
Defined.

  postfix `ᵒᵖᶠ`:(max+2) . opposite_functor
  postfix `ᵒᵖ'`:(max+2) . opposite_functor_rev

Definition functor_id_op (C : Precategory) : (1 : C ⇒ C)ᵒᵖᶠ = 1.
  idp

Definition opposite_rev_opposite_functor (F : Cᵒᵖ ⇒ Dᵒᵖ) : Fᵒᵖ' ᵒᵖᶠ = F.
Proof.
  fapply functor_eq: esimp =>
  { intro c c' f, esimp, exact !id_right @ !id_left}
Defined.

Definition opposite_opposite_rev_functor (F : C ⇒ D) : Fᵒᵖᶠᵒᵖ' = F.
Proof.
  fapply functor_eq: esimp =>
  { intro c c' f, esimp, exact !id_leftright}
Defined.

Definition opposite_compose (G : D ⇒ E) (F : C ⇒ D) : (G of F)ᵒᵖᶠ = Gᵒᵖᶠ of Fᵒᵖᶠ.
  idp

Definition opposite_nat_trans {F G : C ⇒ D} (η : F ⟹ G) : Gᵒᵖᶠ ⟹ Fᵒᵖᶠ.
Proof.
    fapply nat_trans.mk: esimp,
    { intro c, exact η c},
    { intro c c' f, exact !naturality^-1},
Defined.

Definition opposite_rev_nat_trans {F G : Cᵒᵖ ⇒ Dᵒᵖ} (η : F ⟹ G) : Gᵒᵖ' ⟹ Fᵒᵖ'.
Proof.
    fapply nat_trans.mk: esimp,
    { intro c, exact η c},
    { intro c c' f, exact !(@naturality Cᵒᵖ Dᵒᵖ)^-1},
Defined.

Definition opposite_nat_trans_rev {F G : C ⇒ D} (η : Fᵒᵖᶠ ⟹ Gᵒᵖᶠ) : G ⟹ F.
Proof.
    fapply nat_trans.mk: esimp,
    { intro c, exact η c},
    { intro c c' f, exact !(@naturality Cᵒᵖ Dᵒᵖ _ _ η)^-1},
Defined.

Definition opposite_rev_nat_trans_rev {F G : Cᵒᵖ ⇒ Dᵒᵖ} (η : Fᵒᵖ' ⟹ Gᵒᵖ') : G ⟹ F.
Proof.
    fapply nat_trans.mk: esimp,
    { intro c, exact η c},
    { intro c c' f, exact (naturality η f)^-1},
Defined.

Definition opposite_iso {ob : Type} [C : precategory ob] {a b : ob}
    (H : @iso _ C a b) : @iso _ (opposite C) a b.
Proof.
    fapply @iso.MK _ (opposite C),
    { exact to_inv H},
    { exact to_hom H},
    { exact to_left_inverse  H},
    { exact to_right_inverse H},
Defined.

Definition iso_of_opposite_iso  {ob : Type} [C : precategory ob] {a b : ob}
    (H : @iso _ (opposite C) a b) : @iso _ C a b.
Proof.
    fapply iso.MK,
    { exact to_inv H},
    { exact to_hom H},
    { exact to_left_inverse  H},
    { exact to_right_inverse H},
Defined.

Definition opposite_iso_equiv  {ob : Type} [C : precategory ob] (a b : ob)
    : @iso _ (opposite C) a b <~> @iso _ C a b.
Proof.
    fapply equiv.MK,
    { exact iso_of_opposite_iso},
    { exact opposite_iso},
    { intro H, apply iso_eq, reflexivity},
    { intro H, apply iso_eq, reflexivity},
Defined.

Definition is_univalent_opposite (C : Category) : is_univalent (Opposite C).
Proof.
    intro x y,
    fapply is_equiv_of_equiv_of_homotopy,
    { refine @eq_equiv_iso C C x y @e _, symmetry, esimp at *, apply opposite_iso_equiv},
    { intro p, induction p, reflexivity}
Defined.

Definition category_opposite (C : Category) : category (Opposite C).
  category.mk _ (is_univalent_opposite C)

Definition Category_opposite (C : Category) : Category.
  Category.mk _ (category_opposite C)

Defined. category
