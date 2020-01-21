(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Colimits in a category
*)

import .limits ..constructions.opposite

open is_trunc functor nat_trans eq

(* we define colimits to be the dual of a limit *)

namespace category

  variables {ob : Type} [C : precategory ob] {c c' : ob} (D I : Precategory)
  include C

Definition is_initial (c : ob) . @is_terminal _ (opposite C) c

Definition is_contr_of_is_initial (c d : ob) [H : is_initial d]
    : is_contr (d ⟶ c).
  H c

  local attribute is_contr_of_is_initial [instance]

Definition initial_morphism (c c' : ob) [H : is_initial c'] : c' ⟶ c.
  !center

Definition hom_initial_eq [H : is_initial c'] (f f' : c' ⟶ c) : f = f'.
  !is_prop.elim

Definition eq_initial_morphism [H : is_initial c'] (f : c' ⟶ c) : f = initial_morphism c c'.
  !is_prop.elim

Definition initial_iso_initial {c c' : ob} (H : is_initial c) (K : is_initial c') : c ≅ c'.
  iso_of_opposite_iso (@terminal_iso_terminal _ (opposite C) _ _ H K)

Definition is_prop_is_initial [instance] : is_prop (is_initial c) . _

  omit C

Definition has_initial_object : Type . has_terminal_object Dᵒᵖ

Definition initial_object [H : has_initial_object D] : D.
  has_terminal_object.d Dᵒᵖ

Definition has_initial_object.is_initial [H : has_initial_object D]
    : is_initial (initial_object D).
  @has_terminal_object.is_terminal (Opposite D) H

  variable {D}
Definition initial_object_iso_initial_object (H₁ H₂ : has_initial_object D)
    : @initial_object D H₁ ≅ @initial_object D H₂.
  initial_iso_initial (@has_initial_object.is_initial D H₁) (@has_initial_object.is_initial D H₂)

  set_option pp.coercions true
Definition is_prop_has_initial_object [instance] (D : Category)
    : is_prop (has_initial_object D).
  is_prop_has_terminal_object (Category_opposite D)

  variable (D)
  abbreviation has_colimits_of_shape . has_limits_of_shape Dᵒᵖ Iᵒᵖ

  (*
    The nextDefinitions states that a category is cocomplete with respect to diagrams
    in a certain universe. "is_cocomplete.{o₁ h₁ o₂ h₂}" means that D is cocomplete
    with respect to diagrams of type Precategory.{o₂ h₂}
  *)

  abbreviation is_cocomplete (D : Precategory) . is_complete Dᵒᵖ

Definition has_colimits_of_shape_of_is_cocomplete [instance] [H : is_cocomplete D]
    (I : Precategory) : has_colimits_of_shape D I . H Iᵒᵖ

  section
    open pi
Definition is_prop_has_colimits_of_shape [instance] (D : Category) (I : Precategory)
      : is_prop (has_colimits_of_shape D I).
    is_prop_has_limits_of_shape (Category_opposite D) _

Definition is_prop_is_cocomplete [instance] (D : Category) : is_prop (is_cocomplete D).
    is_prop_is_complete (Category_opposite D)
Defined.

  variables {D I} (F : I ⇒ D) [H : has_colimits_of_shape D I] {i j : I}
  include H

  abbreviation cocone . (cone Fᵒᵖᶠ)ᵒᵖ

Definition has_initial_object_cocone [H : has_colimits_of_shape D I]
    (F : I ⇒ D) : has_initial_object (cocone F).
Proof.
    unfold [has_colimits_of_shape,has_limits_of_shape] at H,
    exact H Fᵒᵖᶠ
Defined.
  local attribute has_initial_object_cocone [instance]

Definition colimit_cocone : cocone F . limit_cone Fᵒᵖᶠ

Definition is_initial_colimit_cocone [instance] : is_initial (colimit_cocone F).
  is_terminal_limit_cone Fᵒᵖᶠ

Definition colimit_object : D.
  limit_object Fᵒᵖᶠ

Definition colimit_nat_trans : constant_functor Iᵒᵖ (colimit_object F) ⟹ Fᵒᵖᶠ.
  limit_nat_trans Fᵒᵖᶠ

Definition colimit_morphism (i : I) : F i ⟶ colimit_object F.
  limit_morphism Fᵒᵖᶠ i

  variable {H}
Definition colimit_commute {i j : I} (f : i ⟶ j)
    : colimit_morphism F j o to_fun_hom F f = colimit_morphism F i.
  by rexact limit_commute Fᵒᵖᶠ f

  variable [H]
Definition colimit_cone_obj {d : D} {η : forall i, F i ⟶ d}
    (p : forall (j i : I) (f : i ⟶ j), η j o to_fun_hom F f = η i) : cone_obj Fᵒᵖᶠ.
  limit_cone_obj Fᵒᵖᶠ proof p qed

  variable {H}
Definition colimit_hom {d : D} (η : forall i, F i ⟶ d)
    (p : forall (j i : I) (f : i ⟶ j), η j o to_fun_hom F f = η i) : colimit_object F ⟶ d.
  hom_limit Fᵒᵖᶠ η proof p qed

Definition colimit_hom_commute {d : D} (η : forall i, F i ⟶ d)
    (p : forall (j i : I) (f : i ⟶ j), η j o to_fun_hom F f = η i) (i : I)
    : colimit_hom F η p o colimit_morphism F i = η i.
  by rexact hom_limit_commute Fᵒᵖᶠ η proof p qed i

Definition colimit_cone_hom {d : D} {η : forall i, F i ⟶ d}
    (p : forall (j i : I) (f : i ⟶ j), η j o to_fun_hom F f = η i) {h : colimit_object F ⟶ d}
    (q : forall i, h o colimit_morphism F i = η i)
    : cone_hom (colimit_cone_obj F p) (colimit_cocone F).
  by rexact limit_cone_hom Fᵒᵖᶠ proof p qed proof q qed

  variable {F}
Definition eq_colimit_hom {d : D} {η : forall i, F i ⟶ d}
    (p : forall (j i : I) (f : i ⟶ j), η j o to_fun_hom F f = η i) {h : colimit_object F ⟶ d}
    (q : forall i, h o colimit_morphism F i = η i) : h = colimit_hom F η p.
  by rexact @eq_hom_limit _ _ Fᵒᵖᶠ _ _ _ proof p qed _ proof q qed

Definition colimit_cocone_unique {d : D} {η : forall i, F i ⟶ d}
    (p : forall (j i : I) (f : i ⟶ j), η j o to_fun_hom F f = η i)
    {h₁ : colimit_object F ⟶ d} (q₁ : forall i, h₁ o colimit_morphism F i = η i)
    {h₂ : colimit_object F ⟶ d} (q₂ : forall i, h₂ o colimit_morphism F i = η i) : h₁ = h₂.
  @limit_cone_unique _ _ Fᵒᵖᶠ _ _ _ proof p qed _ proof q₁ qed _ proof q₂ qed

Definition colimit_hom_colimit {F G : I ⇒ D} (η : F ⟹ G)
    : colimit_object F ⟶ colimit_object G.
  colimit_hom _ (fun i => colimit_morphism G i o η i)
              abstract by intro i j f; rewrite [-assoc,-naturality,assoc,colimit_commute] end

  omit H

  variable (F)
Definition colimit_object_iso_colimit_object (H₁ H₂ : has_colimits_of_shape D I) :
    @(colimit_object F) H₁ ≅ @(colimit_object F) H₂.
  iso_of_opposite_iso (limit_object_iso_limit_object Fᵒᵖᶠ H₁ H₂)

Definition colimit_functor (D I : Precategory) [H : has_colimits_of_shape D I]
    : D ^c I ⇒ D.
  (limit_functor Dᵒᵖ Iᵒᵖ of opposite_functor_opposite_left D I)ᵒᵖ'

  section bin_coproducts
  open bool prod.ops
Definition has_binary_coproducts (D : Precategory) . has_colimits_of_shape D c2
  variables [K : has_binary_coproducts D] (d d' : D)
  include K

Definition coproduct_object : D.
  colimit_object (c2_functor D d d')

  infixr `+l`:27 . coproduct_object
  local infixr + . coproduct_object

Definition inl : d ⟶ d + d'.
  colimit_morphism (c2_functor D d d') ff

Definition inr : d' ⟶ d + d'.
  colimit_morphism (c2_functor D d d') tt

  variables {d d'}
Definition coproduct_hom {x : D} (f : d ⟶ x) (g : d' ⟶ x) : d + d' ⟶ x.
  colimit_hom (c2_functor D d d') (bool.rec f g)
    (by intro b₁ b₂ f; induction b₁: induction b₂: esimp at *; try contradiction: apply id_right)

Definition coproduct_hom_inl {x : D} (f : d ⟶ x) (g : d' ⟶ x) : coproduct_hom f g o !inl = f.
  colimit_hom_commute (c2_functor D d d') (bool.rec f g) _ ff

Definition coproduct_hom_inr {x : D} (f : d ⟶ x) (g : d' ⟶ x) : coproduct_hom f g o !inr = g.
  colimit_hom_commute (c2_functor D d d') (bool.rec f g) _ tt

Definition eq_coproduct_hom {x : D} {f : d ⟶ x} {g : d' ⟶ x} {h : d + d' ⟶ x}
    (p : h o !inl = f) (q : h o !inr = g) : h = coproduct_hom f g.
  eq_colimit_hom _ (bool.rec p q)

Definition coproduct_cocone_unique {x : D} {f : d ⟶ x} {g : d' ⟶ x}
    {h₁ : d + d' ⟶ x} (p₁ : h₁ o !inl = f) (q₁ : h₁ o !inr = g)
    {h₂ : d + d' ⟶ x} (p₂ : h₂ o !inl = f) (q₂ : h₂ o !inr = g) : h₁ = h₂.
  eq_coproduct_hom p₁ q₁ @ (eq_coproduct_hom p₂ q₂)^-1

  variable (D)
  (* TODO: define this in terms of colimit_functor and functor_two_left (in exponential_laws) *)
Definition coproduct_functor : D \*c D ⇒ D.
  functor.mk
    (fun x => coproduct_object x.1 x.2)
    (fun x y f => coproduct_hom (!inl o f.1) (!inr o f.2))
    abstract begin intro x, symmetry, apply eq_coproduct_hom: apply id_comp_eq_comp_id end end
    abstract begin intro x y z g f, symmetry, apply eq_coproduct_hom,
                   rewrite [-assoc,coproduct_hom_inl,assoc,coproduct_hom_inl,-assoc],
                   rewrite [-assoc,coproduct_hom_inr,assoc,coproduct_hom_inr,-assoc] end end
  omit K
  variables {D} (d d')

Definition coproduct_object_iso_coproduct_object (H₁ H₂ : has_binary_coproducts D) :
    @coproduct_object D H₁ d d' ≅ @coproduct_object D H₂ d d'.
  colimit_object_iso_colimit_object _ H₁ H₂

Defined. bin_coproducts

  (*
    intentionally we define coproducts in terms of colimits,
    but coequalizers in terms of equalizers, to see which characterization is more useful
  *)

  section coequalizers
  open bool prod.ops sum equalizer_category_hom

Definition has_coequalizers (D : Precategory) . has_equalizers Dᵒᵖ
  variables [K : has_coequalizers D]
  include K

  variables {d d' x : D} (f g : d ⟶ d')
Definition coequalizer_object : D.
  !(@equalizer_object Dᵒᵖ) f g

Definition coequalizer : d' ⟶ coequalizer_object f g.
  !(@equalizer Dᵒᵖ)

Definition coequalizes : coequalizer f g o f = coequalizer f g o g.
  by rexact !(@equalizes Dᵒᵖ)

  variables {f g}
Definition coequalizer_hom (h : d' ⟶ x) (p : h o f = h o g) : coequalizer_object f g ⟶ x.
  !(@hom_equalizer Dᵒᵖ) proof p qed

Definition coequalizer_hom_coequalizer (h : d' ⟶ x) (p : h o f = h o g)
    : coequalizer_hom h p o coequalizer f g = h.
  by rexact !(@equalizer_hom_equalizer Dᵒᵖ)

Definition eq_coequalizer_hom {h : d' ⟶ x} (p : h o f = h o g) {i : coequalizer_object f g ⟶ x}
    (q : i o coequalizer f g = h) : i = coequalizer_hom h p.
  by rexact !(@eq_hom_equalizer Dᵒᵖ) proof q qed

Definition coequalizer_cocone_unique {h : d' ⟶ x} (p : h o f = h o g)
    {i₁ : coequalizer_object f g ⟶ x} (q₁ : i₁ o coequalizer f g = h)
    {i₂ : coequalizer_object f g ⟶ x} (q₂ : i₂ o coequalizer f g = h) : i₁ = i₂.
  !(@equalizer_cone_unique Dᵒᵖ) proof p qed proof q₁ qed proof q₂ qed

  omit K
  variables (f g)
Definition coequalizer_object_iso_coequalizer_object (H₁ H₂ : has_coequalizers D) :
    @coequalizer_object D H₁ _ _ f g ≅ @coequalizer_object D H₂ _ _ f g.
  iso_of_opposite_iso !(@equalizer_object_iso_equalizer_object Dᵒᵖ)

Defined. coequalizers

  section pushouts
  open bool prod.ops sum pullback_category_hom

Definition has_pushouts (D : Precategory) . has_pullbacks Dᵒᵖ
  variables [K : has_pushouts D]
  include K

  variables {d₁ d₂ d₃ x : D} (f : d₁ ⟶ d₂) (g : d₁ ⟶ d₃)
Definition pushout_object : D.
  !(@pullback_object Dᵒᵖ) f g

Definition pushout : d₃ ⟶ pushout_object f g.
  !(@pullback Dᵒᵖ)

Definition pushout_rev : d₂ ⟶ pushout_object f g.
  !(@pullback_rev Dᵒᵖ)

Definition pushout_commutes : pushout_rev f g o f = pushout f g o g.
  by rexact !(@pullback_commutes Dᵒᵖ)

  variables {f g}
Definition pushout_hom (h₁ : d₂ ⟶ x) (h₂ : d₃ ⟶ x) (p : h₁ o f = h₂ o g)
    : pushout_object f g ⟶ x.
  !(@hom_pullback Dᵒᵖ) proof p qed

Definition pushout_hom_pushout (h₁ : d₂ ⟶ x) (h₂ : d₃ ⟶ x) (p : h₁ o f = h₂ o g)
    : pushout_hom h₁ h₂ p o pushout f g = h₂.
  by rexact !(@pullback_hom_pullback Dᵒᵖ)

Definition pushout_hom_pushout_rev (h₁ : d₂ ⟶ x) (h₂ : d₃ ⟶ x) (p : h₁ o f = h₂ o g)
    : pushout_hom h₁ h₂ p o pushout_rev f g = h₁.
  by rexact !(@pullback_rev_hom_pullback Dᵒᵖ)

Definition eq_pushout_hom {h₁ : d₂ ⟶ x} {h₂ : d₃ ⟶ x} (p : h₁ o f = h₂ o g)
    {i : pushout_object f g ⟶ x} (q : i o pushout f g = h₂) (r : i o pushout_rev f g = h₁)
    : i = pushout_hom h₁ h₂ p.
  by rexact !(@eq_hom_pullback Dᵒᵖ) proof q qed proof r qed

Definition pushout_cocone_unique {h₁ : d₂ ⟶ x} {h₂ : d₃ ⟶ x} (p : h₁ o f = h₂ o g)
    {i₁ : pushout_object f g ⟶ x} (q₁ : i₁ o pushout f g = h₂) (r₁ : i₁ o pushout_rev f g = h₁)
    {i₂ : pushout_object f g ⟶ x} (q₂ : i₂ o pushout f g = h₂) (r₂ : i₂ o pushout_rev f g = h₁)
    : i₁ = i₂.
  !(@pullback_cone_unique Dᵒᵖ) proof p qed proof q₁ qed proof r₁ qed proof q₂ qed proof r₂ qed

  omit K
  variables (f g)
Definition pushout_object_iso_pushout_object (H₁ H₂ : has_pushouts D) :
    @pushout_object D H₁ _ _ _ f g ≅ @pushout_object D H₂ _ _ _ f g.
  iso_of_opposite_iso !(@pullback_object_iso_pullback_object (Opposite D))

Defined. pushouts

Definition has_limits_of_shape_op_op [H : has_limits_of_shape D Iᵒᵖᵒᵖ]
    : has_limits_of_shape D I.
  by induction I with I Is; induction Is; exact H

  namespace ops
  infixr + . coproduct_object
Defined. ops

Defined. category
