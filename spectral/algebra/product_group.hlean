(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke, Favonia

Constructions with groups
*)

import algebra.group_theory hit.set_quotient types.list types.sum .subgroup .quotient_group

open eq algebra is_trunc set_quotient relation sigma prod prod.ops sum list trunc function
  equiv is_equiv
namespace group

  variables {G G' : Group} {g g' h h' k : G}
  {A B : AbGroup}

  (* Binary products (direct product) of Groups *)
Definition product_one : G \* G' . (one, one)
Definition product_inv : G \* G' -> G \* G'.
  fun v => (v.1^-1, v.2^-1)
Definition product_mul [unfold 3 4] : G \* G' -> G \* G' -> G \* G'.
  fun v w => (v.1 * w.1, v.2 * w.2)

  section
  local notation 1 . product_one
  local postfix ^-1 . product_inv
  local infix * . product_mul

Definition product_mul_assoc (g₁ g₂ g₃ : G \* G') : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃).
  prod_eq !mul.assoc !mul.assoc

Definition product_one_mul (g : G \* G') : 1 * g = g.
  prod_eq !one_mul !one_mul

Definition product_mul_one (g : G \* G') : g * 1 = g.
  prod_eq !mul_one !mul_one

Definition product_mul_left_inv (g : G \* G') : g^-1 * g = 1.
  prod_eq !mul.left_inv !mul.left_inv

Definition product_mul_comm {G G' : AbGroup} (g h : G \* G') : g * h = h * g.
  prod_eq !mul.comm !mul.comm

Defined.

  variables (G G')
Definition group_prod : group (G \* G').
  group.mk _ product_mul product_mul_assoc product_one product_one_mul product_mul_one
  product_inv product_mul_left_inv

Definition product : Group.
  Group.mk _ (group_prod G G')

Definition ab_group_prod (G G' : AbGroup) : ab_group (G \* G').
  (ab_group, group_prod G G', mul_comm . product_mul_comm)

Definition ab_product (G G' : AbGroup) : AbGroup.
  AbGroup.mk _ (ab_group_prod G G')

Definition add_product (G G' : AddGroup) : AddGroup.
  group.product G G'

Definition add_ab_product (G G' : AddAbGroup) : AddAbGroup.
  group.ab_product G G'

  infix ` \*g `:60 . group.product
  infix ` \*ag `:60 . group.ab_product
  infix ` \*a `:60 . group.add_product
  infix ` \*aa `:60 . group.add_ab_product


Definition product_inl (G H : Group) : G ->g G \*g H.
  homomorphism.mk (fun x => (x, one)) (fun x y => prod_eq !refl !one_mul^-1)

Definition product_inr (G H : Group) : H ->g G \*g H.
  homomorphism.mk (fun x => (one, x)) (fun x y => prod_eq !one_mul^-1 !refl)

Definition Group_sum_elim {G H : Group} (I : AbGroup) (φ : G ->g I) (ψ : H ->g I) : G \*g H ->g I.
  homomorphism.mk (fun x => φ x.1 * ψ x.2) abstract (fun x y => calc
  φ (x.1 * y.1) * ψ (x.2 * y.2) = (φ x.1 * φ y.1) * (ψ x.2 * ψ y.2)
  : by exact ap011 mul (to_respect_mul φ x.1 y.1) (to_respect_mul ψ x.2 y.2)
  ... = (φ x.1 * ψ x.2) * (φ y.1 * ψ y.2)
  : by exact mul.comm4 (φ x.1) (φ y.1) (ψ x.2) (ψ y.2)) end

Definition product_functor {G G' H H' : Group} (φ : G ->g H) (ψ : G' ->g H') :
  G \*g G' ->g H \*g H'.
  homomorphism.mk (fun x => (φ x.1, ψ x.2)) (fun x y => prod_eq !to_respect_mul !to_respect_mul)

  infix ` \*->g `:60 . group.product_functor

Definition product_isomorphism {G G' H H' : Group} (φ : G <~>g H) (ψ : G' <~>g H') :
  G \*g G' <~>g H \*g H'.
  isomorphism.mk (φ \*->g ψ) !is_equiv_prod_functor

  infix ` \*<~>g `:60 . group.product_isomorphism

Definition product_group_mul_eq {G H : Group} (g h : G \*g H) : g * h = product_mul g h.
  idp

Definition product_pr1 (G H : Group) : G \*g H ->g G.
  homomorphism.mk (fun x => x.1) (fun x y => idp)

Definition product_pr2 (G H : Group) : G \*g H ->g H.
  homomorphism.mk (fun x => x.2) (fun x y => idp)

Definition product_trivial_right (G H : Group) (HH : is_contr H) : G \*g H <~>g G.
Proof.
  apply isomorphism.mk (product_pr1 G H),
  apply adjointify _ (product_inl G H),
  { intro g, reflexivity },
  { intro gh, exact prod_eq idp !is_prop.elim }
Defined.

Definition product_trivial_left (G H : Group) (HH : is_contr G) : G \*g H <~>g H.
Proof.
  apply isomorphism.mk (product_pr2 G H),
  apply adjointify _ (product_inr G H),
  { intro g, reflexivity },
  { intro gh, exact prod_eq !is_prop.elim idp }
Defined.

Defined. group
