(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Adjoint functors
*)

import .attributes .examples

open functor nat_trans is_trunc eq iso prod

namespace category

  structure adjoint {C D : Precategory} (F : C ⇒ D) (G : D ⇒ C).
    (η : 1 ⟹ G of F)
    (ε : F of G ⟹ 1)
    (H : forall (c : C), ε (F c) o F (η c) = ID (F c))
    (K : forall (d : D), G (ε d) o η (G d) = ID (G d))

  abbreviation to_unit           . @adjoint.η
  abbreviation to_counit         . @adjoint.ε
  abbreviation to_counit_unit_eq . @adjoint.H
  abbreviation to_unit_counit_eq . @adjoint.K

  (* TODO: define is_left_adjoint in terms of adjoint: *)
  (* structure is_left_adjoint (F : C ⇒ D) . *)
  (*   (G : D ⇒ C) (* G *) *)
  (*   (is_adjoint : adjoint F G) *)

  infix ` ⊣ `:55 . adjoint

  structure is_left_adjoint [class] {C D : Precategory} (F : C ⇒ D).
    (G : D ⇒ C)
    (η : 1 ⟹ G of F)
    (ε : F of G ⟹ 1)
    (H : forall (c : C), ε (F c) o F (η c) = ID (F c))
    (K : forall (d : D), G (ε d) o η (G d) = ID (G d))

  abbreviation right_adjoint  . @is_left_adjoint.G
  abbreviation unit           . @is_left_adjoint.η
  abbreviation counit         . @is_left_adjoint.ε
  abbreviation counit_unit_eq . @is_left_adjoint.H
  abbreviation unit_counit_eq . @is_left_adjoint.K

  section

  variables {C D : Precategory} {F : C ⇒ D} {G : D ⇒ C}

Definition is_left_adjoint_of_adjoint (H : F ⊣ G) : is_left_adjoint F.
Proof.
    induction H with η ε H K, exact is_left_adjoint.mk G η ε H K
Defined.

Definition adjoint_opposite (H : F ⊣ G) : Gᵒᵖᶠ ⊣ Fᵒᵖᶠ.
Proof.
    fconstructor,
    { rexact opposite_nat_trans (to_counit H)},
    { rexact opposite_nat_trans (to_unit H)},
    { rexact to_unit_counit_eq H},
    { rexact to_counit_unit_eq H}
Defined.

Definition adjoint_of_opposite (H : Fᵒᵖᶠ ⊣ Gᵒᵖᶠ) : G ⊣ F.
Proof.
    fconstructor,
    { rexact opposite_rev_nat_trans (to_counit H)},
    { rexact opposite_rev_nat_trans (to_unit H)},
    { rexact to_unit_counit_eq H},
    { rexact to_counit_unit_eq H}
Defined.


Definition is_prop_is_left_adjoint [instance] {C : Category} {D : Precategory} (F : C ⇒ D)
    : is_prop (is_left_adjoint F).
Proof.
    apply is_prop.mk,
    intro G G', cases G with G η ε H K, cases G' with G' η' ε' H' K',
    have lem₁ : forall (p : G = G'), p # η = η' -> p # ε = ε'
      -> is_left_adjoint.mk G η ε H K = is_left_adjoint.mk G' η' ε' H' K',
    begin
      intros p q r, induction p, induction q, induction r, esimp,
      apply apd011 (is_left_adjoint.mk G η ε) !is_prop.elim !is_prop.elimo
    end,
    have lem₂ : forall (d : carrier D),
                    (to_fun_hom G (natural_map ε' d) o
                    natural_map η (to_fun_ob G' d)) o
                    to_fun_hom G' (natural_map ε d) o
                    natural_map η' (to_fun_ob G d) = id =>
    begin
      intro d, esimp,
      rewrite [assoc],
      rewrite [-assoc (G (ε' d))],
      esimp, rewrite [nf_fn_eq_fn_nf_pt' G' ε η d],
      esimp, rewrite [assoc],
      esimp, rewrite [-assoc],
      rewrite [↑functor.compose => -respect_comp G],
      rewrite [nf_fn_eq_fn_nf_pt ε ε' d,nf_fn_eq_fn_nf_pt η' η (G d),▸*],
      rewrite [respect_comp G],
      rewrite [assoc,▸*,-assoc (G (ε d))],
      rewrite [↑functor.compose => -respect_comp G],
      rewrite [H' (G d)],
      rewrite [respect_id,▸*,id_right],
      apply K
    end,
    have lem₃ : forall (d : carrier D),
                    (to_fun_hom G' (natural_map ε d) o
                    natural_map η' (to_fun_ob G d)) o
                    to_fun_hom G (natural_map ε' d) o
                    natural_map η (to_fun_ob G' d) = id =>
    begin
      intro d, esimp,
      rewrite [assoc, -assoc (G' (ε d))],
      esimp, rewrite [nf_fn_eq_fn_nf_pt' G ε' η' d],
      esimp, rewrite [assoc], esimp, rewrite [-assoc],
      rewrite [↑functor.compose => -respect_comp G'],
      rewrite [nf_fn_eq_fn_nf_pt ε' ε d,nf_fn_eq_fn_nf_pt η η' (G' d)],
      esimp,
      rewrite [respect_comp G'],
      rewrite [assoc,▸*,-assoc (G' (ε' d))],
      rewrite [↑functor.compose => -respect_comp G'],
      rewrite [H (G' d)],
      rewrite [respect_id,▸*,id_right],
      apply K'
    end,
    fapply lem₁,
    { fapply functor.eq_of_pointwise_iso =>
      { fapply change_natural_map,
        { exact (G' ofn1 ε) on !assoc_natural_rev on (η' o1nf G)},
        { intro d, exact (G' (ε d) o η' (G d))},
        { intro d, exact ap (fun x => _ o x) !id_left}},
      { intro d, fconstructor,
        { exact (G (ε' d) o η (G' d))},
        { exact lem₂ d },
        { exact lem₃ d }}},
    { clear lem₁, refine transport_hom_of_eq_right _ η @ _,
      krewrite hom_of_eq_compose_right,
      rewrite functor.hom_of_eq_eq_of_pointwise_iso =>
      apply nat_trans_eq, intro c, esimp,
      refine !assoc^-1 @ ap (fun x => _ o x) (nf_fn_eq_fn_nf_pt η η' c) @ !assoc @ _,
      esimp, rewrite [-respect_comp G',H c,respect_id G',▸*,id_left]},
   { clear lem₁, refine transport_hom_of_eq_left _ ε @ _,
     krewrite inv_of_eq_compose_left,
     rewrite functor.inv_of_eq_eq_of_pointwise_iso =>
     apply nat_trans_eq, intro d, esimp,
     krewrite [respect_comp],
     rewrite [assoc,nf_fn_eq_fn_nf_pt ε' ε d,-assoc,▸*,H (G' d),id_right]}
   end

Defined.

  section
  universe variables u v w z
  parameters {C : Precategory.{u v}} {D : Precategory.{w v}} {F : C ⇒ D} {G : D ⇒ C}
          (θ : hom_functor D of prod_functor_prod Fᵒᵖᶠ 1 ≅ hom_functor C of prod_functor_prod 1 G)
  include θ

Definition adj_unit : 1 ⟹ G of F.
Proof.
    fapply nat_trans.mk: esimp,
    { intro c, exact natural_map (to_hom θ) (c, F c) id},
    { intro c c' f,
      note H . naturality (to_hom θ) (ID c, F f),
      note K . ap10 H id,
      rewrite [▸* at K, id_right at K, ▸*, K, respect_id, +id_right],
      clear H K,
      note H . naturality (to_hom θ) (f, ID (F c')),
      note K . ap10 H id,
      rewrite [▸* at K, respect_id at K,+id_left at K, K]}
Defined.

Definition adj_counit : F of G ⟹ 1.
Proof.
    fapply nat_trans.mk: esimp,
    { intro d, exact natural_map (to_inv θ) (G d, d) id, },
    { intro d d' g,
      note H . naturality (to_inv θ) (Gᵒᵖᶠ g, ID d'),
      note K . ap10 H id,
      rewrite [▸* at K, id_left at K, ▸*, K, respect_id, +id_left],
      clear H K,
      note H . naturality (to_inv θ) (ID (G d), g),
      note K . ap10 H id,
      rewrite [▸* at K, respect_id at K,+id_right at K, K]}
Defined.

Definition adj_eq_unit (c : C) (d : D) (f : F c ⟶ d)
    : natural_map (to_hom θ) (c, d) f = G f o adj_unit c.
Proof.
    esimp,
    note H . naturality (to_hom θ) (ID c, f),
    note K . ap10 H id,
    rewrite [▸* at K, id_right at K, K, respect_id, +id_right],
Defined.

Definition adj_eq_counit (c : C) (d : D) (g : c ⟶ G d)
    : natural_map (to_inv θ) (c, d) g = adj_counit d o F g.
Proof.
    esimp,
    note H . naturality (to_inv θ) (g, ID d),
    note K . ap10 H id,
    rewrite [▸* at K, id_left at K, K, respect_id, +id_left],
Defined.

Definition adjoint.mk' : F ⊣ G.
Proof.
    fapply adjoint.mk,
    { exact adj_unit},
    { exact adj_counit},
    { intro c, esimp, refine (adj_eq_counit c (F c) (adj_unit c))^-1 @ _,
      apply ap10 (to_left_inverse (componentwise_iso θ (c, F c)))},
    { intro d, esimp, refine (adj_eq_unit (G d) d (adj_counit d))^-1 @ _,
      apply ap10 (to_right_inverse (componentwise_iso θ (G d, d)))},
Defined.

Defined.


  section
  universe variables u v
  parameters {C D : Precategory.{u v}} (F : C ⇒ D) (U : D -> C)
  (ε : forall d, F (U d) ⟶ d) (θ : forall {c : C} {d : D} (g : F c ⟶ d), c ⟶ U d)
  (θ_coh : forall {c : C} {d : D} (g : F c ⟶ d), ε d o F (θ g) = g)
  (θ_unique : forall {c : C} {d : D} {g : F c ⟶ d} {f : c ⟶ U d}, ε d o F f = g -> θ g = f)

  include θ_coh θ_unique
Definition right_adjoint_simple : D ⇒ C.
Proof.
    fconstructor,
    { exact U },
    { intro d d' g, exact θ (g o ε d) },
    { intro d, apply θ_unique, refine idp o2 !respect_id @ !id_right @ !id_left^-1 },
    { intro d₁ d₂ d₃ g' g, apply θ_unique, refine idp o2 !respect_comp @ !assoc @ _,
      refine !θ_coh o2 idp @ !assoc' @ idp o2 !θ_coh @ !assoc, }
Defined.

Definition bijection_simple : hom_functor D of prod_functor_prod Fᵒᵖᶠ 1 ≅
    hom_functor C of prod_functor_prod 1 right_adjoint_simple.
Proof.
    fapply natural_iso.MK,
    { intro x f, exact θ f },
    { esimp, intro x x' f, apply eq_of_homotopy, intro g, symmetry, apply θ_unique,
      refine idp o2 !respect_comp @ !assoc @ _, refine !θ_coh o2 idp @ !assoc' @ idp o2 _,
      refine idp o2 !respect_comp @ !assoc @ !θ_coh o2 idp },
    { esimp, intro x f, exact ε _ o F f },
    { esimp, intro x, apply eq_of_homotopy, intro g, exact θ_coh g },
    { esimp, intro x, apply eq_of_homotopy, intro g, exact θ_unique idp }
Defined.

Definition is_left_adjoint.mk_simple : is_left_adjoint F.
  is_left_adjoint_of_adjoint (adjoint.mk' bijection_simple)

Defined.

Defined. category
