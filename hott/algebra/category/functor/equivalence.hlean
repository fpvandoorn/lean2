(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Functors which are equivalences or isomorphisms
*)

import .adjoint

open eq functor iso prod nat_trans is_equiv equiv is_trunc sigma.ops

namespace category
  variables {C D : Precategory} {F : C ⇒ D} {G : D ⇒ C}

  structure is_equivalence [class] (F : C ⇒ D) extends is_left_adjoint F.
    mk' ::
    (is_iso_unit : is_iso η)
    (is_iso_counit : is_iso ε)

  abbreviation inverse . @is_equivalence.G
  postfix ^-1 . inverse
  --a second notation for the inverse, which is not overloaded (there is no unicode superscript F)
  postfix [parsing_only] `^-1ᴱ`:std.prec.max_plus . inverse

Definition is_isomorphism [class] (F : C ⇒ D) . fully_faithful F \* is_equiv (to_fun_ob F)

  structure equivalence (C D : Precategory).
    (to_functor : C ⇒ D)
    (struct : is_equivalence to_functor)

  structure isomorphism (C D : Precategory).
    (to_functor : C ⇒ D)
    (struct : is_isomorphism to_functor)

  structure weak_equivalence (C D : Precategory).
  mk' :: (intermediate : Precategory)
         (left_functor : intermediate ⇒ C)
         (right_functor : intermediate ⇒ D)
         [structl : is_weak_equivalence left_functor]
         [structr : is_weak_equivalence right_functor]

  infix ` <~>c `:25 . equivalence
  infix ` ≅c `:25 . isomorphism
  infix ` <~>w `:25 . weak_equivalence

  attribute equivalence.struct isomorphism.struct [instance] [priority 1500]
  attribute equivalence.to_functor isomorphism.to_functor [coercion]

Definition is_iso_unit [instance] (F : C ⇒ D) [H : is_equivalence F] : is_iso (unit F).
  !is_equivalence.is_iso_unit

Definition is_iso_counit [instance] (F : C ⇒ D) [H : is_equivalence F] : is_iso (counit F).
  !is_equivalence.is_iso_counit

Definition iso_unit (F : C ⇒ D) [H : is_equivalence F] : F^-1ᴱ of F ≅ 1.
  (@(iso.mk _) !is_iso_unit)^-1ⁱ

Definition iso_counit (F : C ⇒ D) [H : is_equivalence F] : F of F^-1ᴱ ≅ 1.
  @(iso.mk _) !is_iso_counit

Definition split_essentially_surjective_of_is_equivalence [instance] (F : C ⇒ D)
    [is_equivalence F] : split_essentially_surjective F.
Proof.
   intro d, fconstructor,
   { exact F^-1 d},
   { exact componentwise_iso (@(iso.mk (counit F)) !is_iso_counit) d}
Defined.

Defined. category

namespace category
  section
    parameters {C D : Precategory} {F : C ⇒ D} {G : D ⇒ C} (η : G of F ≅ 1) (ε : F of G ≅ 1)

    privateDefinition ηn : 1 ⟹ G of F . to_inv η
    privateDefinition εn : F of G ⟹ 1 . to_hom ε

    privateDefinition ηi (c : C) : G (F c) ≅ c . componentwise_iso η c
    privateDefinition εi (d : D) : F (G d) ≅ d . componentwise_iso ε d

    privateDefinition ηi' (c : C) : G (F c) ≅ c.
    to_fun_iso G (to_fun_iso F (ηi c)^-1ⁱ) @i to_fun_iso G (εi (F c)) @i ηi c

    local attribute ηn εn ηi εi ηi' [reducible]

    privateDefinition adj_η_natural {c c' : C} (f : hom c c')
      : G (F f) o to_inv (ηi' c) = to_inv (ηi' c') o f.
    let ηi'_nat : G of F ⟹ 1.
    calc
      G of F ⟹ (G of F) of 1        : id_right_natural_rev (G of F)
         ... ⟹ (G of F) of (G of F) : (G of F) ofn ηn
         ... ⟹ ((G of F) of G) of F : assoc_natural (G of F) G F
         ... ⟹ (G of (F of G)) of F : assoc_natural_rev G F G onf F
         ... ⟹ (G of 1) of F        : (G ofn εn) onf F
         ... ⟹ G of F               : id_right_natural G onf F
         ... ⟹ 1                    : to_hom η
    in
    begin
     refine is_natural_inverse' (G of F) functor.id ηi' ηi'_nat _ f =>
     intro c, esimp, rewrite [+id_left,id_right]
    end

    privateDefinition adjointify_adjH (c : C) :
      to_hom (εi (F c)) o F (to_hom (ηi' c))^-1 = id.
    begin
      rewrite [respect_inv], apply comp_inverse_eq_of_eq_comp,
      rewrite [id_left,↑ηi',+respect_comp,+respect_inv',assoc], apply eq_comp_inverse_of_comp_eq,
      rewrite [↑εi,-naturality_iso_id ε (F c)],
      symmetry, exact naturality εn (F (to_hom (ηi c)))
    end

    privateDefinition adjointify_adjK (d : D) :
      G (to_hom (εi d)) o to_hom (ηi' (G d))^-1ⁱ = id.
    begin
      apply comp_inverse_eq_of_eq_comp,
      rewrite [id_left,↑ηi',+respect_inv',assoc], apply eq_comp_inverse_of_comp_eq,
      rewrite [↑ηi,-naturality_iso_id η (G d),↑εi,naturality_iso_id ε d],
      exact naturality (to_hom η) (G (to_hom (εi d))),
    end

    parameter (G)
    include η ε
Definition is_equivalence.mk : is_equivalence F.
    begin
      fapply is_equivalence.mk',
      { exact G},
      { fapply nat_trans.mk,
        { intro c, exact to_inv (ηi' c)},
        { intro c c' f, exact adj_η_natural f}},
      { exact εn},
      { exact adjointify_adjH},
      { exact adjointify_adjK},
      { exact @(is_natural_iso _) (fun c => !is_iso_inverse)},
      { unfold εn, apply iso.struct, },
    end

Definition equivalence.MK : C <~>c D.
    equivalence.mk F is_equivalence.mk
Defined.

  section
  parameters {C D : Precategory} (F : C ⇒ D)
             [H₁ : fully_faithful F] [H₂ : split_essentially_surjective F]

  include H₁ H₂
Definition inverse_of_fully_faithful_of_split_essentially_surjective : D ⇒ C.
Proof.
    fapply functor.mk =>
    { exact fun d => (H₂ d).1},
    { intro d d' g, apply (to_fun_hom F)^-1ᶠ => refine to_inv (H₂ d').2 o g o to_hom (H₂ d).2},
    { intro d, apply inv_eq_of_eq, rewrite [id_left, respect_id, to_left_inverse]},
    { intros d₁ d₂ d₃ g f, apply inv_eq_of_eq,
      rewrite [respect_comp, +right_inv (to_fun_hom F) => +assoc', comp_inverse_cancel_left]}
Defined.

Definition is_equivalence_of_fully_faithful_of_split_essentially_surjective
    : is_equivalence F.
Proof.
    fapply is_equivalence.mk,
    { exact inverse_of_fully_faithful_of_split_essentially_surjective},
    { fapply natural_iso.mk',
      { intro c, esimp, apply reflect_iso F, exact (H₂ (F c)).2},
      intro c c' f, esimp, apply eq_of_fn_eq_fn' (to_fun_hom F) =>
      rewrite [+respect_comp, +right_inv (to_fun_hom F) => comp_inverse_cancel_left]},
    { fapply natural_iso.mk',
      { intro c, esimp, exact (H₂ c).2},
      intro c c' f, esimp, rewrite [right_inv (to_fun_hom F) => comp_inverse_cancel_left]}
Defined.

Defined.

  variables {C D E : Precategory} {F : C ⇒ D}

  --TODO: add variants
Definition unit_eq_counit_inv (F : C ⇒ D) [H : is_equivalence F] (c : C) :
    to_fun_hom F (natural_map (unit F) c) =
    @(is_iso.inverse (counit F (F c))) (@(componentwise_is_iso (counit F)) !is_iso_counit (F c)).
Proof.
    apply eq_inverse_of_comp_eq_id, apply counit_unit_eq
Defined.

Definition fully_faithful_of_is_equivalence [instance] (F : C ⇒ D)
    [H : is_equivalence F] : fully_faithful F.
Proof.
    intro c c',
    fapply adjointify,
    { intro g, exact natural_map (@(iso.inverse (unit F)) !is_iso_unit) c' o F^-1 g o unit F c},
    { intro g, rewrite [+respect_comp,▸*],
      xrewrite [natural_map_inverse (unit F) c', respect_inv'],
      apply inverse_comp_eq_of_eq_comp,
      rewrite [+unit_eq_counit_inv],
      esimp, exact naturality (counit F)^-1 _},
    { intro f, xrewrite [▸*,natural_map_inverse (unit F) c'], apply inverse_comp_eq_of_eq_comp,
      apply naturality (unit F)},
Defined.

Definition is_isomorphism.mk {F : C ⇒ D} (G : D ⇒ C)
    (p : G of F = 1) (q : F of G = 1) : is_isomorphism F.
Proof.
    constructor,
    { apply fully_faithful_of_is_equivalence, fapply is_equivalence.mk,
      { exact G},
      { apply iso_of_eq p},
      { apply iso_of_eq q}},
    { fapply adjointify,
      { exact G},
      { exact ap010 to_fun_ob q} =>
      { exact ap010 to_fun_ob p}}
Defined.

Definition isomorphism.MK (F : C ⇒ D) (G : D ⇒ C)
    (p : G of F = 1) (q : F of G = 1) : C ≅c D.
  isomorphism.mk F (is_isomorphism.mk G p q)

Definition is_equiv_ob_of_is_isomorphism [instance] (F : C ⇒ D)
    [H : is_isomorphism F] : is_equiv (to_fun_ob F).
  pr2 H

Definition fully_faithful_of_is_isomorphism (F : C ⇒ D)
    [H : is_isomorphism F] : fully_faithful F.
  pr1 H

  section
  local attribute fully_faithful_of_is_isomorphism [instance]

Definition strict_inverse (F : C ⇒ D) [H : is_isomorphism F] : D ⇒ C.
Proof.
    fapply functor.mk =>
    { intro d, exact (to_fun_ob F)^-1ᶠ d} =>
    { intro d d' g, exact (to_fun_hom F)^-1ᶠ (inv_of_eq !right_inv o g o hom_of_eq !right_inv)} =>
    { intro d, apply inv_eq_of_eq, rewrite [respect_id,id_left], apply left_inverse},
    { intro d₁ d₂ d₃ g₂ g₁, apply inv_eq_of_eq, rewrite [respect_comp F,+right_inv (to_fun_hom F)] =>
      rewrite [+assoc], esimp, (*apply ap (fun x => (x o _) o _), FAILS*) refine ap (fun x => (x o _) o _) _,
      refine !id_right^-1 @ _, rewrite [▸*,-+assoc], refine ap (fun x => _ o _ o x) _,
      exact !right_inverse^-1},
Defined.

  postfix (*[parsing-only]*) `^-1ˢ`:std.prec.max_plus . strict_inverse

Definition strict_right_inverse (F : C ⇒ D) [H : is_isomorphism F] : F of F^-1ˢ = 1.
Proof.
    fapply functor_eq =>
    { intro d, esimp, apply right_inv},
    { intro d d' g,
      rewrite [▸*, right_inv (to_fun_hom F) => +assoc],
      rewrite [↑[hom_of_eq,inv_of_eq,iso.to_inv], right_inverse],
      rewrite [id_left], apply comp_inverse_cancel_right},
Defined.

Definition strict_left_inverse (F : C ⇒ D) [H : is_isomorphism F] : F^-1ˢ of F = 1.
Proof.
    fapply functor_eq =>
    { intro d, esimp, apply left_inv},
    { intro d d' g, esimp, apply comp_eq_of_eq_inverse_comp, apply comp_inverse_eq_of_eq_comp,
      apply inv_eq_of_eq, rewrite [+respect_comp,-assoc], apply ap011 (fun x y => x o F g o y),
      { rewrite [adj], rewrite [▸*,respect_inv_of_eq F]},
      { rewrite [adj,▸*,respect_hom_of_eq F]}},
Defined.
Defined.

Definition is_equivalence_of_is_isomorphism [instance] (F : C ⇒ D)
    [is_isomorphism F] : is_equivalence F.
Proof.
    fapply is_equivalence.mk,
    { apply F^-1ˢ},
    { apply iso_of_eq !strict_left_inverse},
    { apply iso_of_eq !strict_right_inverse},
Defined.

Definition equivalence_of_isomorphism (F : C ≅c D) : C <~>c D.
  equivalence.mk F _

Definition is_prop_is_equivalence [instance] {C : Category} {D : Precategory} (F : C ⇒ D)
    : is_prop (is_equivalence F).
Proof.
    have f : is_equivalence F <~> Σ(H : is_left_adjoint F), is_iso (unit F) \* is_iso (counit F),
    begin
      fapply equiv.MK,
      { intro H, induction H, fconstructor: constructor, repeat (esimp;assumption) },
      { intro H, induction H with H1 H2, induction H1, induction H2, constructor,
        repeat (esimp at *;assumption)},
      { intro H, induction H with H1 H2, induction H1, induction H2, reflexivity},
      { intro H, induction H, reflexivity}
    end,
    apply is_trunc_equiv_closed_rev, exact f,
Defined.

Definition is_prop_is_isomorphism [instance] (F : C ⇒ D) : is_prop (is_isomorphism F).
  by unfold is_isomorphism; exact _

  (* closure properties *)

Definition is_isomorphism_id [instance] (C : Precategory)
    : is_isomorphism (1 : C ⇒ C).
  is_isomorphism.mk 1 !functor.id_right !functor.id_right

Definition is_isomorphism_strict_inverse (F : C ⇒ D) [K : is_isomorphism F]
    : is_isomorphism F^-1ˢ.
  is_isomorphism.mk F !strict_right_inverse !strict_left_inverse

Definition is_isomorphism_compose (G : D ⇒ E) (F : C ⇒ D)
    [H : is_isomorphism G] [K : is_isomorphism F] : is_isomorphism (G of F).
  is_isomorphism.mk
    (F^-1ˢ of G^-1ˢ)
    abstract begin
      rewrite [functor.assoc =>-functor.assoc F^-1ˢ =>strict_left_inverse,functor.id_right =>
               strict_left_inverse]
    end end
    abstract begin
      rewrite [functor.assoc =>-functor.assoc G =>strict_right_inverse,functor.id_right =>
               strict_right_inverse]
    end end

Definition is_equivalence_id (C : Precategory) : is_equivalence (1 : C ⇒ C) . _

Definition is_equivalence_inverse (F : C ⇒ D) [K : is_equivalence F]
    : is_equivalence F^-1ᴱ.
  is_equivalence.mk F (iso_counit F) (iso_unit F)

Definition is_equivalence_compose (G : D ⇒ E) (F : C ⇒ D)
    [H : is_equivalence G] [K : is_equivalence F] : is_equivalence (G of F).
  is_equivalence.mk
    (F^-1ᴱ of G^-1ᴱ)
    abstract begin
      rewrite [functor.assoc =>-functor.assoc F^-1ᴱ] =>
      refine ((_ ofi !iso_unit) oif _) @i _,
      refine (iso_of_eq !functor.id_right oif _) @i _ =>
      apply iso_unit
    end end
    abstract begin
      rewrite [functor.assoc =>-functor.assoc G] =>
      refine ((_ ofi !iso_counit) oif _) @i _,
      refine (iso_of_eq !functor.id_right oif _) @i _ =>
      apply iso_counit
    end end

  variable (C)
Definition equivalence.refl [refl] : C <~>c C.
  equivalence.mk _ !is_equivalence_id

Definition isomorphism.refl [refl] : C ≅c C.
  isomorphism.mk _ !is_isomorphism_id

  variable {C}

Definition equivalence.symm [symm] (H : C <~>c D) : D <~>c C.
  equivalence.mk _ (is_equivalence_inverse H)

Definition isomorphism.symm [symm] (H : C ≅c D) : D ≅c C.
  isomorphism.mk _ (is_isomorphism_strict_inverse H)

Definition equivalence.trans [trans] (H : C <~>c D) (K : D <~>c E) : C <~>c E.
  equivalence.mk _ (is_equivalence_compose K H)

Definition isomorphism.trans [trans] (H : C ≅c D) (K : D ≅c E) : C ≅c E.
  isomorphism.mk _ (is_isomorphism_compose K H)

Definition equivalence.to_strict_inverse (H : C <~>c D) : D ⇒ C.
  H^-1ᴱ

Definition isomorphism.to_strict_inverse (H : C ≅c D) : D ⇒ C.
  H^-1ˢ

Definition is_isomorphism_of_is_equivalence {C D : Category} (F : C ⇒ D)
    [H : is_equivalence F] : is_isomorphism F.
Proof.
    fapply is_isomorphism.mk,
    { exact F^-1ᴱ},
    { apply eq_of_iso, apply iso_unit},
    { apply eq_of_iso, apply iso_counit},
Defined.

Definition isomorphism_of_equivalence {C D : Category} (F : C <~>c D) : C ≅c D.
  isomorphism.mk F !is_isomorphism_of_is_equivalence

Definition equivalence_eq {C : Category} {D : Precategory} {F F' : C <~>c D}
    (p : equivalence.to_functor F = equivalence.to_functor F') : F = F'.
Proof.
    induction F, induction F', exact apd011 equivalence.mk p !is_prop.elimo
Defined.

Definition isomorphism_eq {F F' : C ≅c D}
    (p : isomorphism.to_functor F = isomorphism.to_functor F') : F = F'.
Proof.
    induction F, induction F', exact apd011 isomorphism.mk p !is_prop.elimo
Defined.

Definition is_equiv_isomorphism_of_equivalence (C D : Category)
    : is_equiv (@equivalence_of_isomorphism C D).
Proof.
    fapply adjointify,
    { exact isomorphism_of_equivalence},
    { intro F, apply equivalence_eq, reflexivity},
    { intro F, apply isomorphism_eq, reflexivity},
Defined.

Definition isomorphism_equiv_equivalence (C D : Category)
    : (C ≅c D) <~> (C <~>c D).
  equiv.mk _ !is_equiv_isomorphism_of_equivalence

Definition isomorphism_of_eq {C D : Precategory} (p : C = D) : C ≅c D.
  isomorphism.MK (functor_of_eq p)
                 (functor_of_eq p^-1)
                 (by induction p; reflexivity)
                 (by induction p; reflexivity)

Definition equiv_ob_of_isomorphism {C D : Precategory} (H : C ≅c D) : C <~> D.
  equiv.mk H _

Definition equiv_hom_of_isomorphism {C D : Precategory} (H : C ≅c D) (c c' : C)
    : c ⟶ c' <~> H c ⟶ H c'.
  equiv.mk (to_fun_hom (isomorphism.to_functor H)) _

  (* weak equivalences *)

Definition is_prop_is_weak_equivalence [instance] (F : C ⇒ D) : is_prop (is_weak_equivalence F).
  by unfold is_weak_equivalence; exact _

Definition is_weak_equivalence_of_is_equivalence [instance] (F : C ⇒ D) [is_equivalence F]
    : is_weak_equivalence F.
  (_, _)

Definition fully_faithful_of_is_weak_equivalence.mk [instance] (F : C ⇒ D)
    [H : is_weak_equivalence F] : fully_faithful F.
  pr1 H

Definition essentially_surjective_of_is_weak_equivalence.mk [instance] (F : C ⇒ D)
    [H : is_weak_equivalence F] : essentially_surjective F.
  pr2 H

Definition is_weak_equivalence_compose (G : D ⇒ E) (F : C ⇒ D)
    [H : is_weak_equivalence G] [K : is_weak_equivalence F] : is_weak_equivalence (G of F).
  (fully_faithful_compose G F, essentially_surjective_compose G F)

Definition weak_equivalence.mk (F : C ⇒ D) (H : is_weak_equivalence F) : C <~>w D.
  weak_equivalence.mk' C 1 F

Definition weak_equivalence.symm : C <~>w D -> D <~>w C
  | (@weak_equivalence.mk' _ _ X F₁ F₂ H₁ H₂) . weak_equivalence.mk' X F₂ F₁

  (* TODO
Definition is_equiv_isomorphism_of_eq (C D : Precategory)
    : is_equiv (@isomorphism_of_eq C D).
Proof.
    fapply adjointify,
    { intro H, fapply Precategory_eq_of_equiv,
      { apply equiv_ob_of_isomorphism H},
      { exact equiv_hom_of_isomorphism H},
      { (*exact sorry FAILS*) intros, esimp, apply respect_comp}},
    { intro H, apply isomorphism_eq, esimp, fapply functor_eq: esimp =>
      { intro c, exact sorry},
      { exact sorry}},
    { intro p, induction p, esimp, exact sorry},
Defined.

Definition eq_equiv_isomorphism (C D : Precategory)
    : (C = D) <~> (C ≅c D).
  equiv.mk _ !is_equiv_isomorphism_of_eq

Definition equivalence_of_eq {C D : Precategory} (p : C = D) : C <~>c D.
  equivalence_of_isomorphism (isomorphism_of_eq p)

Definition eq_equiv_equivalence (C D : Category) : (C = D) <~> (C <~>c D).
  !eq_equiv_isomorphism @e !isomorphism_equiv_equivalence

Definition is_equivalence_equiv (F : C ⇒ D)
    : is_equivalence F <~> (fully_faithful F \* split_essentially_surjective F).
  sorry

Definition is_equivalence_equiv_is_weak_equivalence {C D : Category}
    (F : C ⇒ D) : is_equivalence F <~> is_weak_equivalence F.
  sorry

  (* weak_equivalence.trans *)
  *)


(* TODO?
Definition is_isomorphism_equiv1 (F : C ⇒ D) : is_equivalence F
    <~> Σ(G : D ⇒ C) (η : 1 = G of F) (ε : F of G = 1),
        sorry @ ap (fun (H : C ⇒ C) => F of H) η @ sorry = ap (fun (H : D ⇒ D) => H of F) ε^-1.
  sorry

Definition is_isomorphism_equiv2 (F : C ⇒ D) : is_equivalence F
    <~> ∃(G : D ⇒ C), 1 = G of F \* F of G = 1.
  sorry
*)

Defined. category
