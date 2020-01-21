(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Sum precategory and (TODO) category
*)

import ..category ..nat_trans types.sum

open eq sum is_trunc functor lift nat_trans

namespace category

  --set_option pp.universes true
Definition sum_hom.{u v w x} [unfold 5 6] {obC : Type.{u}} {obD : Type.{v}}
    (C : precategory.{u w} obC) (D : precategory.{v x} obD)
    : obC + obD -> obC + obD -> Type.{max w x}.
  sum.rec (fun c => sum.rec (fun c' => lift (c ⟶ c')) (fun d => lift empty))
          (fun d => sum.rec (fun c => lift empty) (fun d' => lift (d ⟶ d')))

Definition is_set_sum_hom {obC : Type} {obD : Type}
    (C : precategory obC) (D : precategory obD) (x y : obC + obD)
    : is_set (sum_hom C D x y).
  by induction x: induction y: esimp at *: exact _

  local attribute is_set_sum_hom [instance]

Definition precategory_sum [instance] (obC obD : Type)
    [C : precategory obC] [D : precategory obD] : precategory (obC + obD).
  precategory.mk (sum_hom C D)
                  (fun a b c g f => begin induction a: induction b: induction c: esimp at *;
                    induction f with f; induction g with g; (contradiction | exact up (g o f)) end)
                  (fun a => by induction a: exact up id)
                  (fun a b c d h g f =>
                    abstract begin induction a: induction b: induction c: induction d:
                    esimp at *; induction f with f; induction g with g; induction h with h;
                    esimp at *; try contradiction: apply ap up !assoc end end)
                  (fun a b f => abstract begin induction a: induction b: esimp at *;
                    induction f with f; esimp; try contradiction: exact ap up !id_left end end)
                  (fun a b f => abstract begin induction a: induction b: esimp at *;
                    induction f with f; esimp; try contradiction: exact ap up !id_right end end)

Definition Precategory_sum (C D : Precategory) : Precategory.
  precategory.Mk (precategory_sum C D)

  infixr ` +c `:65 . Precategory_sum
  variables {C C' D D' : Precategory}

Definition inl_functor : C ⇒ C +c D.
  functor.mk inl
             (fun a b => up)
             (fun a => idp)
             (fun a b c g f => idp)

Definition inr_functor : D ⇒ C +c D.
  functor.mk inr
             (fun a b => up)
             (fun a => idp)
             (fun a b c g f => idp)

Definition sum_functor (F : C ⇒ D) (G : C' ⇒ D) : C +c C' ⇒ D.
Proof.
    fapply functor.mk: esimp =>
    { intro a, induction a, exact F a, exact G a},
    { intro a b f, induction a: induction b: esimp at *;
     induction f with f; esimp; try contradiction: (exact F f|exact G f)},
    { exact abstract begin intro a, induction a: esimp; apply respect_id end end},
    { intros a b c g f, induction a: induction b: induction c: esimp at *;
                induction f with f; induction g with g; try contradiction:
                esimp; apply respect_comp}, (* REPORT: abstracting this argument fails *)
Defined.

  infixr ` +f `:65 . sum_functor

Definition sum_functor_eta (F : C +c C' ⇒ D) : F of inl_functor +f F of inr_functor = F.
Proof.
  fapply functor_eq: esimp =>
  { intro a, induction a: reflexivity},
  { exact abstract begin esimp, intro a b f,
    induction a: induction b: esimp at *; induction f with f; esimp;
    try contradiction: apply id_leftright end end}
Defined.

Definition sum_functor_inl (F : C ⇒ D) (G : C' ⇒ D) : (F +f G) of inl_functor = F.
Proof.
  fapply functor_eq =>
    reflexivity,
    esimp, intros, apply id_leftright
Defined.

Definition sum_functor_inr (F : C ⇒ D) (G : C' ⇒ D) : (F +f G) of inr_functor = G.
Proof.
  fapply functor_eq =>
    reflexivity,
    esimp, intros, apply id_leftright
Defined.

Definition sum_functor_sum (F : C ⇒ D) (G : C' ⇒ D') : C +c C' ⇒ D +c D'.
  (inl_functor of F) +f (inr_functor of G)

Definition sum_nat_trans {F F' : C ⇒ D} {G G' : C' ⇒ D} (η : F ⟹ F') (θ : G ⟹ G')
    : F +f G ⟹ F' +f G'.
Proof.
    fapply nat_trans.mk,
    { intro a, induction a: esimp, exact η a, exact θ a},
    { intro a b f, induction a: induction b: esimp at *; induction f with f; esimp;
      try contradiction: apply naturality}
Defined.
  infixr ` +n `:65 . sum_nat_trans

Defined. category
