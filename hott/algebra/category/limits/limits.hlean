(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Limits in a category
*)

import ..constructions.cone ..constructions.discrete ..constructions.product
       ..constructions.finite_cats ..category ..constructions.functor

open is_trunc functor nat_trans eq

namespace category

  variables {ob : Type} [C : precategory ob] {c c' : ob} (D I : Precategory)
  include C

Definition is_terminal [class] (c : ob) . forall d, is_contr (d ⟶ c)
Definition is_contr_of_is_terminal (c d : ob) [H : is_terminal d] : is_contr (c ⟶ d).
  H c

  local attribute is_contr_of_is_terminal [instance]

Definition terminal_morphism (c c' : ob) [H : is_terminal c'] : c ⟶ c'.
  !center

Definition hom_terminal_eq [H : is_terminal c'] (f f' : c ⟶ c') : f = f'.
  !is_prop.elim

Definition eq_terminal_morphism [H : is_terminal c'] (f : c ⟶ c') : f = terminal_morphism c c'.
  !is_prop.elim

Definition terminal_iso_terminal (c c' : ob) [H : is_terminal c] [K : is_terminal c']
    : c ≅ c'.
  iso.MK !terminal_morphism !terminal_morphism !hom_terminal_eq !hom_terminal_eq

  local attribute is_terminal [reducible]
Definition is_prop_is_terminal [instance] : is_prop (is_terminal c).
  _

  omit C

  structure has_terminal_object [class] (D : Precategory).
    (d : D)
    (is_terminal : is_terminal d)

Definition terminal_object . @has_terminal_object.d
  attribute has_terminal_object.is_terminal [instance]

  variable {D}
Definition terminal_object_iso_terminal_object (H₁ H₂ : has_terminal_object D)
    : @terminal_object D H₁ ≅ @terminal_object D H₂.
  !terminal_iso_terminal

Definition is_prop_has_terminal_object [instance] (D : Category)
    : is_prop (has_terminal_object D).
Proof.
    apply is_prop.mk, intro t₁ t₂, induction t₁ with d₁ H₁, induction t₂ with d₂ H₂,
    have p : d₁ = d₂,
    begin apply eq_of_iso, apply terminal_iso_terminal end,
    induction p, exact ap _ !is_prop.elim
Defined.

  variable (D)
Definition has_limits_of_shape [class] . forall (F : I ⇒ D), has_terminal_object (cone F)

  (*
    The nextDefinitions states that a category is complete with respect to diagrams
    in a certain universe. "is_complete.{o₁ h₁ o₂ h₂}" means that D is complete
    with respect to diagrams with shape in Precategory.{o₂ h₂}
  *)

Definition is_complete.{o₁ h₁ o₂ h₂} [class] (D : Precategory.{o₁ h₁}).
  forall (I : Precategory.{o₂ h₂}), has_limits_of_shape D I

Definition has_limits_of_shape_of_is_complete [instance] [H : is_complete D] (I : Precategory)
    : has_limits_of_shape D I . H I

  section
    open pi
Definition is_prop_has_limits_of_shape [instance] (D : Category) (I : Precategory)
      : is_prop (has_limits_of_shape D I).
    by apply is_trunc_pi; intro F; exact is_prop_has_terminal_object (Category_cone F)

    local attribute is_complete [reducible]
Definition is_prop_is_complete [instance] (D : Category) : is_prop (is_complete D) . _
Defined.

  variables {D I}
Definition has_terminal_object_cone [H : has_limits_of_shape D I]
    (F : I ⇒ D) : has_terminal_object (cone F) . H F
  local attribute has_terminal_object_cone [instance]

  variables (F : I ⇒ D) [H : has_limits_of_shape D I] {i j : I}
  include H

Definition limit_cone : cone F . !terminal_object

Definition is_terminal_limit_cone [instance] : is_terminal (limit_cone F).
  has_terminal_object.is_terminal _

  section specific_limit
  omit H
  variable {F}
  variables (x : cone_obj F) [K : is_terminal x]
  include K

Definition to_limit_object : D.
  cone_to_obj x

Definition to_limit_nat_trans : constant_functor I (to_limit_object x) ⟹ F.
  cone_to_nat x

Definition to_limit_morphism (i : I) : to_limit_object x ⟶ F i.
  to_limit_nat_trans x i

Definition to_limit_commute {i j : I} (f : i ⟶ j)
    : to_fun_hom F f o to_limit_morphism x i = to_limit_morphism x j.
  naturality (to_limit_nat_trans x) f @ !id_right

Definition to_limit_cone_obj {d : D} {η : forall i, d ⟶ F i}
    (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j) : cone_obj F.
  cone_obj.mk d (nat_trans.mk η (fun a b f => p f @ !id_right^-1))

Definition to_hom_limit {d : D} (η : forall i, d ⟶ F i)
    (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j) : d ⟶ to_limit_object x.
  cone_to_hom (terminal_morphism (to_limit_cone_obj x p) x)

Definition to_hom_limit_commute {d : D} (η : forall i, d ⟶ F i)
    (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j) (i : I)
    : to_limit_morphism x i o to_hom_limit x η p = η i.
  cone_to_eq (terminal_morphism (to_limit_cone_obj x p) x) i

Definition to_limit_cone_hom {d : D} {η : forall i, d ⟶ F i}
    (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j) {h : d ⟶ to_limit_object x}
    (q : forall i, to_limit_morphism x i o h = η i)
    : cone_hom (to_limit_cone_obj x p) x.
  cone_hom.mk h q

  variable {x}
Definition to_eq_hom_limit {d : D} {η : forall i, d ⟶ F i}
    (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j) {h : d ⟶ to_limit_object x}
    (q : forall i, to_limit_morphism x i o h = η i) : h = to_hom_limit x η p.
  ap cone_to_hom (eq_terminal_morphism (to_limit_cone_hom x p q))

Definition to_limit_cone_unique {d : D} {η : forall i, d ⟶ F i}
    (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j)
    {h₁ : d ⟶ to_limit_object x} (q₁ : forall i, to_limit_morphism x i o h₁ = η i)
    {h₂ : d ⟶ to_limit_object x} (q₂ : forall i, to_limit_morphism x i o h₂ = η i): h₁ = h₂.
  to_eq_hom_limit p q₁ @ (to_eq_hom_limit p q₂)^-1

  omit K
Definition to_limit_object_iso_to_limit_object (x y : cone_obj F)
    [K : is_terminal x] [L : is_terminal y] : to_limit_object x ≅ to_limit_object y.
  cone_iso_pr1 !terminal_iso_terminal

Defined. specific_limit

  (*
    TODO: relate belowDefinitions to aboveDefinitions.
    However, type class resolution seems to fail...
  *)

Definition limit_object : D.
  cone_to_obj (limit_cone F)

Definition limit_nat_trans : constant_functor I (limit_object F) ⟹ F.
  cone_to_nat (limit_cone F)

Definition limit_morphism (i : I) : limit_object F ⟶ F i.
  limit_nat_trans F i

  variable {H}
Definition limit_commute {i j : I} (f : i ⟶ j)
    : to_fun_hom F f o limit_morphism F i = limit_morphism F j.
  naturality (limit_nat_trans F) f @ !id_right

  variable [H]
Definition limit_cone_obj {d : D} {η : forall i, d ⟶ F i}
    (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j) : cone_obj F.
  cone_obj.mk d (nat_trans.mk η (fun a b f => p f @ !id_right^-1))

  variable {H}
Definition hom_limit {d : D} (η : forall i, d ⟶ F i)
    (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j) : d ⟶ limit_object F.
  cone_to_hom (@(terminal_morphism (limit_cone_obj F p) _) (is_terminal_limit_cone _))

Definition hom_limit_commute {d : D} (η : forall i, d ⟶ F i)
    (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j) (i : I)
    : limit_morphism F i o hom_limit F η p = η i.
  cone_to_eq (@(terminal_morphism (limit_cone_obj F p) _) (is_terminal_limit_cone _)) i

Definition limit_cone_hom {d : D} {η : forall i, d ⟶ F i}
    (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j) {h : d ⟶ limit_object F}
    (q : forall i, limit_morphism F i o h = η i) : cone_hom (limit_cone_obj F p) (limit_cone F).
  cone_hom.mk h q

  variable {F}
Definition eq_hom_limit {d : D} {η : forall i, d ⟶ F i}
    (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j) {h : d ⟶ limit_object F}
    (q : forall i, limit_morphism F i o h = η i) : h = hom_limit F η p.
  ap cone_to_hom (@eq_terminal_morphism _ _ _ _ (is_terminal_limit_cone _) (limit_cone_hom F p q))

Definition limit_cone_unique {d : D} {η : forall i, d ⟶ F i}
    (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j)
    {h₁ : d ⟶ limit_object F} (q₁ : forall i, limit_morphism F i o h₁ = η i)
    {h₂ : d ⟶ limit_object F} (q₂ : forall i, limit_morphism F i o h₂ = η i): h₁ = h₂.
  eq_hom_limit p q₁ @ (eq_hom_limit p q₂)^-1

Definition limit_hom_limit {F G : I ⇒ D} (η : F ⟹ G) : limit_object F ⟶ limit_object G.
  hom_limit _ (fun i => η i o limit_morphism F i)
              abstract by intro i j f; rewrite [assoc,naturality,-assoc,limit_commute] end

Definition limit_hom_limit_commute {F G : I ⇒ D} (η : F ⟹ G)
    : limit_morphism G i o limit_hom_limit η = η i o limit_morphism F i.
  !hom_limit_commute

  (*Definition hom_limit_commute {d : D} (η : forall i, d ⟶ F i) *)
  (*   (p : forall (i j : I) (f : i ⟶ j), to_fun_hom F f o η i = η j) (i : I) *)
  (*   : limit_morphism F i o hom_limit F η p = η i . *)
  (* cone_to_eq (@(terminal_morphism (limit_cone_obj F p) _) (is_terminal_limit_cone _)) i *)

  omit H

  variable (F)
Definition limit_object_iso_limit_object (H₁ H₂ : has_limits_of_shape D I) :
    @(limit_object F) H₁ ≅ @(limit_object F) H₂.
  cone_iso_pr1 !terminal_object_iso_terminal_object

Definition limit_functor (D I : Precategory) [H : has_limits_of_shape D I]
    : D ^c I ⇒ D.
Proof.
    fapply functor.mk: esimp =>
    { intro F, exact limit_object F},
    { apply @limit_hom_limit},
    { intro F, unfold limit_hom_limit, refine (eq_hom_limit _ _)^-1, intro i,
      apply comp_id_eq_id_comp},
    { intro F G H η θ, unfold limit_hom_limit, refine (eq_hom_limit _ _)^-1, intro i,
      rewrite [assoc, hom_limit_commute, -assoc, hom_limit_commute, assoc]}
Defined.

  section bin_products
  open bool prod.ops
Definition has_binary_products (D : Precategory) . has_limits_of_shape D c2
  variables [K : has_binary_products D] (d d' : D)
  include K

Definition product_object : D.
  limit_object (c2_functor D d d')

  infixr ` \*l `:75 . product_object

Definition pr1 : d \*l d' ⟶ d.
  limit_morphism (c2_functor D d d') ff

Definition pr2 : d \*l d' ⟶ d'.
  limit_morphism (c2_functor D d d') tt

  variables {d d'}
Definition hom_product {x : D} (f : x ⟶ d) (g : x ⟶ d') : x ⟶ d \*l d'.
  hom_limit (c2_functor D d d') (bool.rec f g)
    (by intro b₁ b₂ f; induction b₁: induction b₂: esimp at *; try contradiction: apply id_left)

Definition pr1_hom_product {x : D} (f : x ⟶ d) (g : x ⟶ d') : !pr1 o hom_product f g = f.
  hom_limit_commute (c2_functor D d d') (bool.rec f g) _ ff

Definition pr2_hom_product {x : D} (f : x ⟶ d) (g : x ⟶ d') : !pr2 o hom_product f g = g.
  hom_limit_commute (c2_functor D d d') (bool.rec f g) _ tt

Definition eq_hom_product {x : D} {f : x ⟶ d} {g : x ⟶ d'} {h : x ⟶ d \*l d'}
    (p : !pr1 o h = f) (q : !pr2 o h = g) : h = hom_product f g.
  eq_hom_limit _ (bool.rec p q)

Definition product_cone_unique {x : D} {f : x ⟶ d} {g : x ⟶ d'}
    {h₁ : x ⟶ d \*l d'} (p₁ : !pr1 o h₁ = f) (q₁ : !pr2 o h₁ = g)
    {h₂ : x ⟶ d \*l d'} (p₂ : !pr1 o h₂ = f) (q₂ : !pr2 o h₂ = g) : h₁ = h₂.
  eq_hom_product p₁ q₁ @ (eq_hom_product p₂ q₂)^-1

  variable (D)
  (* TODO: define this in terms of limit_functor and functor_two_left (in exponential_laws) *)
Definition product_functor : D \*c D ⇒ D.
  functor.mk
    (fun x => product_object x.1 x.2)
    (fun x y f => hom_product (f.1 o !pr1) (f.2 o !pr2))
    abstract begin intro x, symmetry, apply eq_hom_product: apply comp_id_eq_id_comp end end
    abstract begin intro x y z g f, symmetry, apply eq_hom_product,
                   rewrite [assoc,pr1_hom_product,-assoc,pr1_hom_product,assoc],
                   rewrite [assoc,pr2_hom_product,-assoc,pr2_hom_product,assoc] end end
  omit K
  variables {D} (d d')

Definition product_object_iso_product_object (H₁ H₂ : has_binary_products D) :
    @product_object D H₁ d d' ≅ @product_object D H₂ d d'.
  limit_object_iso_limit_object _ H₁ H₂

Defined. bin_products

  section equalizers
  open bool prod.ops sum equalizer_category_hom
Definition has_equalizers (D : Precategory) . has_limits_of_shape D equalizer_category
  variables [K : has_equalizers D]
  include K

  variables {d d' x : D} (f g : d ⟶ d')
Definition equalizer_object : D.
  limit_object (equalizer_category_functor D f g)

Definition equalizer : equalizer_object f g ⟶ d.
  limit_morphism (equalizer_category_functor D f g) ff

Definition equalizes : f o equalizer f g = g o equalizer f g.
   limit_commute (equalizer_category_functor D f g) (inl f1) @
  (limit_commute (equalizer_category_functor D f g) (inl f2))^-1

  variables {f g}
Definition hom_equalizer (h : x ⟶ d) (p : f o h = g o h) : x ⟶ equalizer_object f g.
  hom_limit (equalizer_category_functor D f g)
            (bool.rec h (g o h))
            begin
              intro b₁ b₂ i; induction i with j j: induction j,
              (* report(?) "esimp" is super slow here *)
              exact p, reflexivity, apply id_left
            end

Definition equalizer_hom_equalizer (h : x ⟶ d) (p : f o h = g o h)
    : equalizer f g o hom_equalizer h p = h.
  hom_limit_commute (equalizer_category_functor D f g) (bool.rec h (g o h)) _ ff

Definition eq_hom_equalizer {h : x ⟶ d} (p : f o h = g o h) {i : x ⟶ equalizer_object f g}
    (q : equalizer f g o i = h) : i = hom_equalizer h p.
  eq_hom_limit _ (bool.rec q
    begin
      refine ap (fun x => x o i) (limit_commute (equalizer_category_functor D f g) (inl f2))^-1 @ _ =>
      refine !assoc^-1 @ _,
      exact ap (fun x => _ o x) q
    end)

Definition equalizer_cone_unique {h : x ⟶ d} (p : f o h = g o h)
    {i₁ : x ⟶ equalizer_object f g} (q₁ : equalizer f g o i₁ = h)
    {i₂ : x ⟶ equalizer_object f g} (q₂ : equalizer f g o i₂ = h) : i₁ = i₂.
  eq_hom_equalizer p q₁ @ (eq_hom_equalizer p q₂)^-1

  omit K
  variables (f g)
Definition equalizer_object_iso_equalizer_object (H₁ H₂ : has_equalizers D) :
    @equalizer_object D H₁ _ _ f g ≅ @equalizer_object D H₂ _ _ f g.
  limit_object_iso_limit_object _ H₁ H₂

Defined. equalizers

  section pullbacks
  open sum prod.ops pullback_category_ob pullback_category_hom
Definition has_pullbacks (D : Precategory) . has_limits_of_shape D pullback_category
  variables [K : has_pullbacks D]
  include K

  variables {d₁ d₂ d₃ x : D} (f : d₁ ⟶ d₃) (g : d₂ ⟶ d₃)
Definition pullback_object : D.
  limit_object (pullback_category_functor D f g)

Definition pullback : pullback_object f g ⟶ d₂.
  limit_morphism (pullback_category_functor D f g) BL

Definition pullback_rev : pullback_object f g ⟶ d₁.
  limit_morphism (pullback_category_functor D f g) TR

Definition pullback_commutes : f o pullback_rev f g = g o pullback f g.
   limit_commute (pullback_category_functor D f g) (inl f1) @
  (limit_commute (pullback_category_functor D f g) (inl f2))^-1

  variables {f g}
Definition hom_pullback (h₁ : x ⟶ d₁) (h₂ : x ⟶ d₂) (p : f o h₁ = g o h₂)
    : x ⟶ pullback_object f g.
  hom_limit (pullback_category_functor D f g)
            (pullback_category_ob.rec h₁ h₂ (g o h₂))
            begin
              intro i₁ i₂ k; induction k with j j: induction j,
              exact p, reflexivity, apply id_left
            end

Definition pullback_hom_pullback (h₁ : x ⟶ d₁) (h₂ : x ⟶ d₂) (p : f o h₁ = g o h₂)
    : pullback f g o hom_pullback h₁ h₂ p = h₂.
  hom_limit_commute (pullback_category_functor D f g) (pullback_category_ob.rec h₁ h₂ (g o h₂)) _ BL

Definition pullback_rev_hom_pullback (h₁ : x ⟶ d₁) (h₂ : x ⟶ d₂) (p : f o h₁ = g o h₂)
    : pullback_rev f g o hom_pullback h₁ h₂ p = h₁.
  hom_limit_commute (pullback_category_functor D f g) (pullback_category_ob.rec h₁ h₂ (g o h₂)) _ TR

Definition eq_hom_pullback {h₁ : x ⟶ d₁} {h₂ : x ⟶ d₂} (p : f o h₁ = g o h₂)
    {k : x ⟶ pullback_object f g} (q : pullback f g o k = h₂) (r : pullback_rev f g o k = h₁)
    : k = hom_pullback h₁ h₂ p.
  eq_hom_limit _ (pullback_category_ob.rec r q
    begin
      refine ap (fun x => x o k) (limit_commute (pullback_category_functor D f g) (inl f2))^-1 @ _ =>
      refine !assoc^-1 @ _,
      exact ap (fun x => _ o x) q
    end)

Definition pullback_cone_unique {h₁ : x ⟶ d₁} {h₂ : x ⟶ d₂} (p : f o h₁ = g o h₂)
    {k₁ : x ⟶ pullback_object f g} (q₁ : pullback f g o k₁ = h₂) (r₁ : pullback_rev f g o k₁ = h₁)
    {k₂ : x ⟶ pullback_object f g} (q₂ : pullback f g o k₂ = h₂) (r₂ : pullback_rev f g o k₂ = h₁)
    : k₁ = k₂.
  (eq_hom_pullback p q₁ r₁) @ (eq_hom_pullback p q₂ r₂)^-1

  variables (f g)
Definition pullback_object_iso_pullback_object (H₁ H₂ : has_pullbacks D) :
    @pullback_object D H₁ _ _ _ f g ≅ @pullback_object D H₂ _ _ _ f g.
  limit_object_iso_limit_object _ H₁ H₂

Defined. pullbacks

  namespace ops
  infixr \*l . product_object
Defined. ops

Defined. category
