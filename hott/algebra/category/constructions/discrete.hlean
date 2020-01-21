(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Discrete category
*)

import ..groupoid types.bool ..nat_trans

open eq is_trunc iso bool functor nat_trans

namespace category

Definition precategory_of_1_type (A : Type) [H : is_trunc 1 A] : precategory A.
  @precategory.mk _ _ (@is_trunc_eq _ _ H)
    (fun (a b c : A) (p : b = c) (q : a = b) => q @ p)
    (fun (a : A) => refl a)
    (fun (a b c d : A) (p : c = d) (q : b = c) (r : a = b) => con.assoc r q p)
    (fun (a b : A) (p : a = b) => con_idp p)
    (fun (a b : A) (p : a = b) => idp_con p)

Definition groupoid_of_1_type (A : Type) [H : is_trunc 1 A] : groupoid A.
  groupoid.mk !precategory_of_1_type
              (fun (a b : A) (p : a = b) => is_iso.mk _ (con_pV _) (con_Vp _))

Definition Precategory_of_1_type (A : Type) [H : is_trunc 1 A] : Precategory.
  precategory.Mk (precategory_of_1_type A)

Definition Groupoid_of_1_type (A : Type) [H : is_trunc 1 A] : Groupoid.
  groupoid.Mk _ (groupoid_of_1_type A)

Definition discrete_precategory (A : Type) [H : is_set A] : precategory A.
  precategory_of_1_type A

Definition discrete_groupoid (A : Type) [H : is_set A] : groupoid A.
  groupoid_of_1_type A

Definition Discrete_precategory (A : Type) [H : is_set A] : Precategory.
  precategory.Mk (discrete_precategory A)

Definition Discrete_groupoid (A : Type) [H : is_set A] : Groupoid.
  groupoid.Mk _ (discrete_groupoid A)

Definition c2 : Precategory . Discrete_precategory bool

Definition c2_functor (C : Precategory) (x y : C) : c2 ⇒ C.
  functor.mk (bool.rec x y)
             (bool.rec (bool.rec (fun f => id) (by contradiction))
                       (bool.rec (by contradiction) (fun f => id)))
             abstract (bool.rec idp idp) end
             abstract begin intro b₁ b₂ b₃ g f, induction b₁: induction b₂: induction b₃:
                            esimp at *: try contradiction: exact !id_id^-1 end end

Definition c2_functor_eta {C : Precategory} (F : c2 ⇒ C) :
    c2_functor C (to_fun_ob F ff) (to_fun_ob F tt) = F.
Proof.
  fapply functor_eq: esimp =>
  { intro b, induction b: reflexivity},
  { intro b₁ b₂ p, induction p, induction b₁: esimp; rewrite [id_leftright]; exact !respect_id^-1}
Defined.

Definition c2_nat_trans {C : Precategory} {x y u v : C} (f : x ⟶ u) (g : y ⟶ v) :
    c2_functor C x y ⟹ c2_functor C u v.
Proof.
  fapply nat_trans.mk: esimp,
  { intro b, induction b, exact f, exact g},
  { intro b₁ b₂ p, induction p, induction b₁: esimp: apply id_comp_eq_comp_id},
Defined.

Defined. category
