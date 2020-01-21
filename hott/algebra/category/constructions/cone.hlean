(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Cones of a diagram in a category
*)

import ..nat_trans ..category

open functor nat_trans eq equiv is_trunc is_equiv iso sigma sigma.ops pi

namespace category

  structure cone_obj {I C : Precategory} (F : I ⇒ C).
  (c : C)
  (η : constant_functor I c ⟹ F)

  variables {I C D : Precategory} {F : I ⇒ C} {x y z : cone_obj F} {i : I}

Definition cone_to_obj . @cone_obj.c
Definition cone_to_nat (c : cone_obj F) : constant_functor I (cone_to_obj c) ⟹ F.
  cone_obj.η c

  local attribute cone_to_obj [coercion]

  structure cone_hom (x y : cone_obj F).
  (f : x ⟶ y)
  (p : forall i, cone_to_nat y i o f = cone_to_nat x i)

Definition cone_to_hom . @cone_hom.f
Definition cone_to_eq (f : cone_hom x y) (i : I)
    : cone_to_nat y i o (cone_to_hom f) = cone_to_nat x i.
  cone_hom.p f i

  local attribute cone_to_hom [coercion]

Definition cone_id (x : cone_obj F) : cone_hom x x.
  cone_hom.mk id
              (fun i => !id_right)

Definition cone_comp (g : cone_hom y z) (f : cone_hom x y) : cone_hom x z.
  cone_hom.mk (cone_to_hom g o cone_to_hom f)
              abstract fun i => by rewrite [assoc, +cone_to_eq] end

Definition cone_obj_eq (p : cone_to_obj x = cone_to_obj y)
    (q : forall i, cone_to_nat x i = cone_to_nat y i o hom_of_eq p) : x = y.
Proof.
    induction x, induction y, esimp at *, induction p, apply ap (cone_obj.mk c),
    apply nat_trans_eq, intro i, exact q i @ !id_right
Defined.

Definition c_cone_obj_eq (p : cone_to_obj x = cone_to_obj y)
    (q : forall i, cone_to_nat x i = cone_to_nat y i o hom_of_eq p) : ap cone_to_obj (cone_obj_eq p q) = p.
Proof.
    induction x, induction y, esimp at *, induction p,
    esimp [cone_obj_eq], rewrite [-ap_compose,↑function.compose =>ap_constant]
Defined.

Definition cone_hom_eq {f f' : cone_hom x y} (q : cone_to_hom f = cone_to_hom f') : f = f'.
Proof.
    induction f, induction f', esimp at *, induction q, apply ap (cone_hom.mk f),
    apply @is_prop.elim, apply pi.is_trunc_pi, intro x, apply is_trunc_eq, (* type class fails *)
Defined.

  variable (F)

Definition precategory_cone [instance] : precategory (cone_obj F).
  @precategory.mk _ cone_hom
                 abstract begin
                   intro x y,
                   have H : cone_hom x y <~> Σ(f : x ⟶ y), forall i, cone_to_nat y i o f = cone_to_nat x i,
                   begin
                     fapply equiv.MK,
                     { intro f, induction f, constructor, assumption},
                     { intro v, induction v, constructor, assumption},
                     { intro v, induction v, reflexivity},
                     { intro f, induction f, reflexivity}
                   end,
                   apply is_trunc.is_trunc_equiv_closed_rev, exact H,
                   fapply sigma.is_trunc_sigma, intros,
                   apply is_trunc_succ, apply pi.is_trunc_pi, intros, esimp,
                   (*exact _,*) (* type class inference fails here *)
                   apply is_trunc_eq,
                 end end
                 (fun x y z => cone_comp)
                 cone_id
                 abstract begin intros, apply cone_hom_eq, esimp, apply assoc    end end
                 abstract begin intros, apply cone_hom_eq, esimp, apply id_left  end end
                 abstract begin intros, apply cone_hom_eq, esimp, apply id_right end end

Definition cone : Precategory.
  precategory.Mk (precategory_cone F)

  variable {F}
Definition cone_iso_pr1 (h : x ≅ y) : cone_to_obj x ≅ cone_to_obj y.
  iso.MK
    (cone_to_hom (to_hom h))
    (cone_to_hom (to_inv h))
    (ap cone_to_hom (to_left_inverse h))
    (ap cone_to_hom (to_right_inverse h))


Definition cone_iso.mk (f : cone_to_obj x ≅ cone_to_obj y)
    (p : forall i, cone_to_nat y i o to_hom f = cone_to_nat x i) : x ≅ y.
Proof.
    fapply iso.MK,
    { exact !cone_hom.mk p},
    { fapply cone_hom.mk,
      { exact to_inv f},
      { intro i, apply comp_inverse_eq_of_eq_comp, exact (p i)^-1}},
    { apply cone_hom_eq, esimp, apply left_inverse},
    { apply cone_hom_eq, esimp, apply right_inverse},
Defined.

  variables (x y)
Definition cone_iso_equiv : (x ≅ y) <~> Σ(f : cone_to_obj x ≅ cone_to_obj y),
                                          forall i, cone_to_nat y i o to_hom f = cone_to_nat x i.
Proof.
    fapply equiv.MK,
    { intro h, exact ⟨cone_iso_pr1 h, cone_to_eq (to_hom h)⟩},
    { intro v, exact cone_iso.mk v.1 v.2},
    { intro v, induction v with f p, fapply sigma_eq: esimp,
      { apply iso_eq, reflexivity},
      { apply is_prop.elimo, apply is_trunc_pi, intro i, apply is_prop_hom_eq}},
    { intro h, esimp, apply iso_eq, apply cone_hom_eq, reflexivity},
Defined.

Definition cone_eq_equiv : (x = y) <~> Σ(f : cone_to_obj x = cone_to_obj y),
                                          forall i, cone_to_nat y i o hom_of_eq f = cone_to_nat x i.
Proof.
    fapply equiv.MK,
    { intro r, fapply sigma.mk, exact ap cone_to_obj r, induction r, intro i, apply id_right},
    { intro v, induction v with p q, induction x with c η, induction y with c' η', esimp at *,
      apply cone_obj_eq p, esimp, intro i, exact (q i)^-1},
    { intro v, induction v with p q, induction x with c η, induction y with c' η', esimp at *,
      induction p, esimp, fapply sigma_eq: esimp,
      { apply c_cone_obj_eq},
      { apply is_prop.elimo, apply is_trunc_pi, intro i, apply is_prop_hom_eq}},
    { intro r, induction r, esimp, induction x, esimp, apply ap02, apply is_prop.elim},
Defined.

  section is_univalent

Definition is_univalent_cone {I : Precategory} {C : Category} (F : I ⇒ C)
      : is_univalent (cone F).
    begin
      intro x y,
      fapply is_equiv_of_equiv_of_homotopy,
      { exact calc
(x = y) <~> (Σ(f : cone_to_obj x = cone_to_obj y), forall i, cone_to_nat y i o hom_of_eq f = cone_to_nat x i)
                  : cone_eq_equiv
    ... <~> (Σ(f : cone_to_obj x ≅ cone_to_obj y), forall i, cone_to_nat y i o to_hom f = cone_to_nat x i)
                  : sigma_equiv_sigma !eq_equiv_iso (fun a => !equiv.refl)
    ... <~> (x ≅ y) : cone_iso_equiv },
      { intro p, induction p, esimp [equiv.trans,equiv.symm], esimp [sigma_functor] =>
        apply iso_eq, reflexivity}
    end

Definition category_cone [instance] {I : Precategory} {C : Category} (F : I ⇒ C)
      : category (cone_obj F).
    category.mk _ (is_univalent_cone F)

Definition Category_cone {I : Precategory} {C : Category} (F : I ⇒ C)
      : Category.
    Category.mk _ (category_cone F)

Defined. is_univalent

Definition cone_obj_compose (G : C ⇒ D) (x : cone_obj F) : cone_obj (G of F).
Proof.
  fapply cone_obj.mk,
  { exact G x},
  { fapply change_natural_map,
    { refine ((G ofn cone_to_nat x) on _), apply nat_trans_of_eq, fapply functor_eq: esimp =>
      intro i j k, esimp, rewrite [id_leftright,respect_id]},
    { intro i, esimp, exact G (cone_to_nat x i)},
    { intro i, esimp, rewrite [ap010_functor_eq => ▸*, id_right]}}
Defined.

Defined. category
