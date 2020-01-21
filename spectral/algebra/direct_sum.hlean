(*
Copyright (c) 2015 Floris van Doorn, Egbert Rijke, Favonia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke, Favonia

Constructions with groups
*)

import .quotient_group .free_abelian_group .product_group

open eq is_equiv algebra is_trunc set_quotient relation sigma prod sum list trunc function equiv sigma.ops lift

namespace group

  section

  parameters {I : Type} [is_set I] (Y : I -> AbGroup)
  variables {A' : AbGroup} {Y' : I -> AbGroup}

  open option pointed

Definition dirsum_carrier : AbGroup . free_ab_group (Σi, Y i)₊

  local abbreviation ι . (@free_ab_group_inclusion (Σi, Y i)₊ _ o some)
  inductive dirsum_rel : dirsum_carrier -> Type.
  | rmk : forall i y₁ y₂, dirsum_rel (ι ⟨i, y₁⟩ * ι ⟨i, y₂⟩ *  (ι ⟨i, y₁ * y₂⟩)^-1)

Definition dirsum : AbGroup . quotient_ab_group_gen dirsum_carrier (fun g => ∥dirsum_rel g∥)

  (*Definition dirsum_carrier_incl (i : I) : Y i ->g dirsum_carrier . *)

Definition dirsum_incl (i : I) : Y i ->g dirsum.
  homomorphism.mk (fun y => class_of (ι ⟨i, y⟩))
Proof. intro g h, symmetry, apply gqg_eq_of_rel, apply tr, apply dirsum_rel.rmk end

  parameter {Y}
Definition dirsum.rec {P : dirsum -> Type} [H : forall g, is_prop (P g)]
  (h₁ : forall i (y : Y i), P (dirsum_incl i y)) (h₂ : P 1) (h₃ : forall g h, P g -> P h -> P (g * h)) :
  forall g, P g.
Proof.
  refine @set_quotient.rec_prop _ _ _ H _,
  refine @set_quotient.rec_prop _ _ _ (fun x => !H) _,
  esimp, intro l, induction l with s l ih,
  { exact h₂ },
  { induction s with z z,
  { induction z with v,
  { refine transport P _ ih, apply ap class_of, symmetry,
  exact eq_of_rel (tr (free_ab_group.fcg_rel.resp_append !free_ab_group.fcg_rel.cancelpt1 (free_ab_group.fcg_rel.rrefl l))) },
  { induction v with i y, exact h₃ _ _ (h₁ i y) ih } },
  { induction z with v,
  { refine transport P _ ih, apply ap class_of, symmetry,
  exact eq_of_rel (tr (free_ab_group.fcg_rel.resp_append !free_ab_group.fcg_rel.cancelpt2 (free_ab_group.fcg_rel.rrefl l))) },
  { induction v with i y,
  refine h₃ (gqg_map _ _ (class_of [inr (some ⟨i, y⟩)])) _ _ ih,
  refine transport P _ (h₁ i y^-1),
  refine _ @ !one_mul,
  refine _ @ ap (fun x => mul x _) (to_respect_zero (dirsum_incl i)),
  apply gqg_eq_of_rel',
  apply tr, esimp,
  refine transport dirsum_rel _ (dirsum_rel.rmk i y^-1 y),
  rewrite [mul.left_inv, mul.assoc]} } }
Defined.

Definition dirsum_homotopy {φ ψ : dirsum ->g A'}
  (h : forall i (y : Y i), φ (dirsum_incl i y) = ψ (dirsum_incl i y)) : φ == ψ.
Proof.
  refine dirsum.rec _ _ _,
  exact h,
  refine !to_respect_zero @ !to_respect_zero^-1,
  intro g₁ g₂ h₁ h₂, rewrite [* to_respect_mul, h₁, h₂]
Defined.

Definition dirsum_elim_resp_quotient (f : forall i, Y i ->g A') (g : dirsum_carrier)
  (r : ∥dirsum_rel g∥) : free_ab_group_elim ((pmap_equiv_left (Σi, Y i) A')^-1 (fun v => f v.1 v.2)) g = 1.
Proof.
  induction r with r, induction r,
  rewrite [to_respect_mul, to_respect_inv, to_respect_mul, ▸*, ↑foldl, *one_mul],
  rewrite [↑pmap_equiv_left], esimp,
  rewrite [-to_respect_mul], apply mul.right_inv
Defined.

Definition dirsum_elim (f : forall i, Y i ->g A') : dirsum ->g A'.
  gqg_elim _ (free_ab_group_elim ((pmap_equiv_left (Σi, Y i) A')^-1 (fun v => f v.1 v.2))) (dirsum_elim_resp_quotient f)

Definition dirsum_elim_compute (f : forall i, Y i ->g A') (i : I) (y : Y i) :
  dirsum_elim f (dirsum_incl i y) = f i y.
Proof.
  apply one_mul
Defined.

Definition dirsum_elim_unique (f : forall i, Y i ->g A') (k : dirsum ->g A')
  (H : forall i, k og dirsum_incl i == f i) : k == dirsum_elim f.
Proof.
  apply gqg_elim_unique,
  apply free_ab_group_elim_unique,
  intro x, induction x with z,
  { esimp, refine _ @ to_respect_zero k, apply ap k, apply ap class_of,
  exact eq_of_rel (tr !free_ab_group.fcg_rel.cancelpt1) },
  { induction z with i y, exact H i y }
Defined.

Defined.

Definition binary_dirsum (G H : AbGroup) : dirsum (bool.rec G H) <~>g G \*ag H.
  let branch . bool.rec G H in
  let to_hom . (dirsum_elim (bool.rec (product_inl G H) (product_inr G H))
  : dirsum (bool.rec G H) ->g G \*ag H) in
  let from_hom . (Group_sum_elim (dirsum (bool.rec G H))
  (dirsum_incl branch bool.ff) (dirsum_incl branch bool.tt)
  : G \*g H ->g dirsum branch) in
Proof.
  fapply isomorphism.mk,
  { exact dirsum_elim (bool.rec (product_inl G H) (product_inr G H)) },
  fapply adjointify,
  { exact from_hom },
  { intro gh, induction gh with g h,
  exact prod_eq (mul_one (1 * g) @ one_mul g) (ap (fun o => o * h) (mul_one 1) @ one_mul h) },
  { refine dirsum.rec _ _ _,
  { intro b x,
  refine ap from_hom (dirsum_elim_compute (bool.rec (product_inl G H) (product_inr G H)) b x) @ _,
  induction b,
  { exact ap (fun y => dirsum_incl branch bool.ff x * y) (to_respect_one (dirsum_incl branch bool.tt)) @ mul_one _ },
  { exact ap (fun y => y * dirsum_incl branch bool.tt x) (to_respect_one (dirsum_incl branch bool.ff)) @ one_mul _ }
  },
  { refine ap from_hom (to_respect_one to_hom) @ to_respect_one from_hom },
  { intro g h gβ hβ,
  refine ap from_hom (to_respect_mul to_hom _ _) @ to_respect_mul from_hom _ _ @ _,
  exact ap011 mul gβ hβ
  }
  }
Defined.

  variables {I J : Type} [is_set I] [is_set J] {Y Y' Y'' : I -> AbGroup}

Definition dirsum_functor (f : forall , Y i ->g Y' i) : dirsum Y ->g dirsum Y'.
  dirsum_elim (fun i => dirsum_incl Y' i og f i)

Definition dirsum_functor_compose (f' : forall , Y' i ->g Y'' i) (f : forall i, Y i ->g Y' i) :
  dirsum_functor f' og dirsum_functor f == dirsum_functor (fun i => f' i og f i).
Proof.
  apply dirsum_homotopy,
  intro i y, reflexivity,
Defined.

  variable (Y)
Definition dirsum_functor_gid : dirsum_functor (fun i => gid (Y i)) == gid (dirsum Y).
Proof.
  apply dirsum_homotopy,
  intro i y, reflexivity,
Defined.
  variable {Y}

Definition dirsum_functor_mul (f f' : forall , Y i ->g Y' i) :
  homomorphism_mul (dirsum_functor f) (dirsum_functor f') ~
  dirsum_functor (fun i => homomorphism_mul (f i) (f' i)).
Proof.
  apply dirsum_homotopy,
  intro i y, exact sorry
Defined.

Definition dirsum_functor_homotopy (f f' : forall , Y i ->g Y' i) (p : f ~2 f') :
  dirsum_functor f == dirsum_functor f'.
Proof.
  apply dirsum_homotopy,
  intro i y, exact sorry
Defined.

Definition dirsum_functor_left (f : J -> I) : dirsum (Y o f) ->g dirsum Y.
  dirsum_elim (fun j => dirsum_incl Y (f j))

Definition dirsum_isomorphism (f : forall i, Y i <~>g Y' i) : dirsum Y <~>g dirsum Y'.
  let to_hom . dirsum_functor (fun i => f i) in
  let from_hom . dirsum_functor (fun i => (f i)^-1ᵍ) in
Proof.
  fapply isomorphism.mk,
  exact dirsum_functor (fun i => f i),
  fapply is_equiv.adjointify,
  exact dirsum_functor (fun i => (f i)^-1ᵍ),
  { intro ds,
  refine (homomorphism_compose_eq (dirsum_functor (fun i => f i)) (dirsum_functor (fun i => (f i)^-1ᵍ)) _)^-1 @ _,
  refine dirsum_functor_compose (fun i => f i) (fun i => (f i)^-1ᵍ) ds @ _,
  refine dirsum_functor_homotopy _ (fun i => !gid) (fun i => to_right_inv (equiv_of_isomorphism (f i))) ds @ _,
  exact !dirsum_functor_gid
  },
  { intro ds,
  refine (homomorphism_compose_eq (dirsum_functor (fun i => (f i)^-1ᵍ)) (dirsum_functor (fun i => f i)) _)^-1 @ _,
  refine dirsum_functor_compose (fun i => (f i)^-1ᵍ) (fun i => f i) ds @ _,
  refine dirsum_functor_homotopy _ (fun i => !gid) (fun i x =>
  proof
  to_left_inv (equiv_of_isomorphism (f i)) x
  qed
  ) ds @ _,
  exact !dirsum_functor_gid
  }
Defined.

Defined. group

namespace group

Definition dirsum_down_left.{u v w} {I : Type.{u}} [is_set I] (Y : I -> AbGroup.{w})
  : dirsum (Y o down.{u v}) <~>g dirsum Y.
  proof
  let to_hom . @dirsum_functor_left _ _ _ _ Y down.{u v} in
  let from_hom . dirsum_elim (fun i => dirsum_incl (Y o down.{u v}) (up.{u v} i)) in
Proof.
  fapply isomorphism.mk,
  { exact to_hom },
  fapply adjointify,
  { exact from_hom },
  { intro ds,
  refine (homomorphism_compose_eq to_hom from_hom ds)^-1 @ _,
  refine @dirsum_homotopy I _ Y (dirsum Y) (to_hom og from_hom) !gid _ ds,
  intro i y,
  refine homomorphism_compose_eq to_hom from_hom _ @ _,
  refine ap to_hom (dirsum_elim_compute (fun i => dirsum_incl (Y o down.{u v}) (up.{u v} i)) i y) @ _,
  refine dirsum_elim_compute _ (up.{u v} i) y @ _,
  reflexivity
  },
  { intro ds,
  refine (homomorphism_compose_eq from_hom to_hom ds)^-1 @ _,
  refine @dirsum_homotopy _ _ (Y o down.{u v}) (dirsum (Y o down.{u v})) (from_hom og to_hom) !gid _ ds,
  intro i y, induction i with i,
  refine homomorphism_compose_eq from_hom to_hom _ @ _,
  refine ap from_hom (dirsum_elim_compute (fun i => dirsum_incl Y (down.{u v} i)) (up.{u v} i) y) @ _,
  refine dirsum_elim_compute _ i y @ _,
  reflexivity
  }
Defined.
  qed

Defined. group
