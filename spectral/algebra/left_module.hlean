(*
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Floris van Doorn

Modules prod vector spaces over a ring.

(We use "left_module," which is more precise, because "module" is a keyword.)
-/
import algebra.field ..move_to_lib .exactness algebra.group_power
open is_trunc pointed function sigma eq algebra prod is_equiv equiv group

structure has_scalar [class] (F V : Type) :=
(smul : F → V → V)

infixl ` • `:73 := has_scalar.smul

(* modules over a ring -/

namespace left_module

structure left_module (R M : Type) [ringR : ring R] extends has_scalar R M, ab_group M renaming
  mul → add mul_assoc → add_assoc one → zero one_mul → zero_add mul_one → add_zero inv → neg
  mul_left_inv → add_left_inv mul_comm → add_comm :=
(smul_left_distrib : Π (r : R) (x y : M), smul r (add x y) = (add (smul r x) (smul r y)))
(smul_right_distrib : Π (r s : R) (x : M), smul (ring.add _ r s) x = (add (smul r x) (smul s x)))
(mul_smul : Π r s x, smul (mul r s) x = smul r (smul s x))
(one_smul : Π x, smul one x = x)

(* we make it a class now (and not as part of the structure) to avoid
  left_module.to_ab_group to be an instance -/
attribute left_module [class]

definition add_ab_group_of_left_module [reducible] [trans_instance] (R M : Type) [K : ring R]
  [H : left_module R M] : add_ab_group M :=
@left_module.to_ab_group R M K H

definition has_scalar_of_left_module [reducible] [trans_instance] (R M : Type) [K : ring R]
  [H : left_module R M] : has_scalar R M :=
@left_module.to_has_scalar R M K H

section left_module
  variables {R M : Type}
  variable  [ringR : ring R]
  variable  [moduleRM : left_module R M]
  include   ringR moduleRM

  -- Note: the anonymous include does not work in the propositions below.

  proposition smul_left_distrib (a : R) (u v : M) : a • (u + v) = a • u + a • v :=
  !left_module.smul_left_distrib

  proposition smul_right_distrib (a b : R) (u : M) : (a + b) • u = a • u + b • u :=
  !left_module.smul_right_distrib

  proposition mul_smul (a : R) (b : R) (u : M) : (a * b) • u = a • (b • u) :=
  !left_module.mul_smul

  proposition one_smul (u : M) : (1 : R) • u = u := !left_module.one_smul

  proposition zero_smul (u : M) : (0 : R) • u = 0 :=
  have (0 : R) • u + 0 • u = 0 • u + 0, by rewrite [-smul_right_distrib, *add_zero],
  !add.left_cancel this

  proposition smul_zero (a : R) : a • (0 : M) = 0 :=
  have a • (0:M) + a • 0 = a • 0 + 0, by rewrite [-smul_left_distrib, *add_zero],
  !add.left_cancel this

  proposition neg_smul (a : R) (u : M) : (-a) • u = - (a • u) :=
  eq_neg_of_add_eq_zero (by rewrite [-smul_right_distrib, add.left_inv, zero_smul])

  proposition neg_one_smul (u : M) : -(1 : R) • u = -u :=
  by rewrite [neg_smul, one_smul]

  proposition smul_neg (a : R) (u : M) : a • (-u) = -(a • u) :=
  by rewrite [-neg_one_smul, -mul_smul, mul_neg_one_eq_neg, neg_smul]

  proposition smul_sub_left_distrib (a : R) (u v : M) : a • (u - v) = a • u - a • v :=
  by rewrite [sub_eq_add_neg, smul_left_distrib, smul_neg]

  proposition sub_smul_right_distrib (a b : R) (v : M) : (a - b) • v = a • v - b • v :=
  by rewrite [sub_eq_add_neg, smul_right_distrib, neg_smul]

end left_module

(* vector spaces -/

structure vector_space [class] (F V : Type) [fieldF : field F]
  extends left_module F V

(* homomorphisms -/

definition is_smul_hom [class] (R : Type) {M₁ M₂ : Type} [has_scalar R M₁] [has_scalar R M₂]
  (f : M₁ → M₂) : Type :=
∀ r : R, ∀ a : M₁, f (r • a) = r • f a

definition is_prop_is_smul_hom [instance] (R : Type) {M₁ M₂ : Type} [is_set M₂]
  [has_scalar R M₁] [has_scalar R M₂] (f : M₁ → M₂) : is_prop (is_smul_hom R f) :=
begin unfold is_smul_hom, apply _ end

definition respect_smul (R : Type) {M₁ M₂ : Type} [has_scalar R M₁] [has_scalar R M₂]
    (f : M₁ → M₂) [H : is_smul_hom R f] :
  ∀ r : R, ∀ a : M₁, f (r • a) = r • f a :=
H

definition is_module_hom [class] (R : Type) {M₁ M₂ : Type}
  [has_scalar R M₁] [has_scalar R M₂] [add_group M₁] [add_group M₂]
  (f : M₁ → M₂) :=
is_add_hom f × is_smul_hom R f

definition is_add_hom_of_is_module_hom [instance] (R : Type) {M₁ M₂ : Type}
  [has_scalar R M₁] [has_scalar R M₂] [add_group M₁] [add_group M₂]
  (f : M₁ → M₂) [H : is_module_hom R f] : is_add_hom f :=
prod.pr1 H

definition is_smul_hom_of_is_module_hom [instance] {R : Type} {M₁ M₂ : Type}
  [has_scalar R M₁] [has_scalar R M₂] [add_group M₁] [add_group M₂]
  (f : M₁ → M₂) [H : is_module_hom R f] : is_smul_hom R f :=
prod.pr2 H

-- Why do we have to give the instance explicitly?
definition is_prop_is_module_hom [instance] (R : Type) {M₁ M₂ : Type}
  [has_scalar R M₁] [has_scalar R M₂] [add_group M₁] [add_group M₂]
  (f : M₁ → M₂) : is_prop (is_module_hom R f) :=
have h₁ : is_prop (is_add_hom f), from is_prop_is_add_hom f,
begin unfold is_module_hom, apply _ end

section module_hom
  variables {R : Type} {M₁ M₂ M₃ : Type}
  variables [has_scalar R M₁] [has_scalar R M₂] [has_scalar R M₃]
  variables [add_group M₁] [add_group M₂] [add_group M₃]
  variables (g : M₂ → M₃) (f : M₁ → M₂) [is_module_hom R g] [is_module_hom R f]

  proposition is_module_hom_id : is_module_hom R (@id M₁) :=
  pair (λ a₁ a₂, rfl) (λ r a, rfl)

  proposition is_module_hom_comp : is_module_hom R (g ∘ f) :=
  pair
    (take a₁ a₂, begin esimp, rewrite [respect_add f, respect_add g] end)
    (take r a, by esimp; rewrite [respect_smul R f, respect_smul R g])

  proposition respect_smul_add_smul (a b : R) (u v : M₁) : f (a • u + b • v) = a • f u + b • f v :=
  by rewrite [respect_add f, +respect_smul R f]

end module_hom

section hom_constant
  variables {R : Type} {M₁ M₂ : Type}
  variables [ring R] [has_scalar R M₁] [add_group M₁] [left_module R M₂]
  proposition is_module_hom_constant : is_module_hom R (const M₁ (0 : M₂)) :=
  (λm₁ m₂, !add_zero⁻¹, λr m, (smul_zero r)⁻¹ᵖ)

end hom_constant

structure LeftModule (R : Ring) :=
(carrier : Type) (struct : left_module R carrier)

attribute LeftModule.struct [instance]

section
local attribute LeftModule.carrier [coercion]

definition AddAbGroup_of_LeftModule [coercion] {R : Ring} (M : LeftModule R) : AddAbGroup :=
AddAbGroup.mk M (LeftModule.struct M)
end

definition LeftModule.struct2 [instance] {R : Ring} (M : LeftModule R) : left_module R M :=
LeftModule.struct M

-- definition LeftModule.struct3 [instance] {R : Ring} (M : LeftModule R) :
--   left_module R (AddAbGroup_of_LeftModule M) :=
-- _


definition pointed_LeftModule_carrier [instance] {R : Ring} (M : LeftModule R) :
  pointed (LeftModule.carrier M) :=
pointed.mk zero

definition pSet_of_LeftModule {R : Ring} (M : LeftModule R) : Set* :=
pSet.mk' (LeftModule.carrier M)

definition left_module_AddAbGroup_of_LeftModule [instance] {R : Ring} (M : LeftModule R) :
  left_module R (AddAbGroup_of_LeftModule M) :=
LeftModule.struct M

definition left_module_AddAbGroup_of_LeftModule2 [instance] {R : Ring} (M : LeftModule R) :
  left_module R (Group_of_AbGroup (AddAbGroup_of_LeftModule M)) :=
LeftModule.struct M

definition left_module_of_ab_group {G : Type} [gG : add_ab_group G] {R : Type} [ring R]
  (smul : R → G → G)
  (h1 : Π (r : R) (x y : G), smul r (x + y) = (smul r x + smul r y))
  (h2 : Π (r s : R) (x : G), smul (r + s) x = (smul r x + smul s x))
  (h3 : Π r s x, smul (r * s) x = smul r (smul s x))
  (h4 : Π x, smul 1 x = x) : left_module R G  :=
left_module.mk smul _ add add.assoc 0 zero_add add_zero neg add.left_inv add.comm h1 h2 h3 h4

definition LeftModule_of_AddAbGroup {R : Ring} (G : AddAbGroup) (smul : R → G → G)
  (h1 h2 h3 h4) : LeftModule R :=
LeftModule.mk G (left_module_of_ab_group smul h1 h2 h3 h4)

open unit
definition trivial_LeftModule [constructor] (R : Ring) : LeftModule R :=
LeftModule_of_AddAbGroup trivial_ab_group (λr u, star)
  (λr u₁ u₂, idp) (λr₁ r₂ u, idp) (λr₁ r₂ u, idp) unit.eta

section
  variables {R : Ring} {M M₁ M₂ M₃ : LeftModule R}

  definition smul_homomorphism [constructor] (M : LeftModule R) (r : R) : M →a M :=
  add_homomorphism.mk (λg, r • g) (smul_left_distrib r)

  proposition to_smul_left_distrib (a : R) (u v : M) : a • (u + v) = a • u + a • v :=
  !smul_left_distrib

  proposition to_smul_right_distrib (a b : R) (u : M) : (a + b) • u = a • u + b • u :=
  !smul_right_distrib

  proposition to_mul_smul (a : R) (b : R) (u : M) : (a * b) • u = a • (b • u) :=
  !mul_smul

  proposition to_one_smul (u : M) : (1 : R) • u = u := !one_smul

  structure homomorphism (M₁ M₂ : LeftModule R) : Type :=
    (fn : LeftModule.carrier M₁ → LeftModule.carrier M₂)
    (p : is_module_hom R fn)

  infix ` →lm `:55 := homomorphism

  definition homomorphism_fn [unfold 4] [coercion] := @homomorphism.fn

  definition is_module_hom_of_homomorphism [unfold 4] [instance] [priority 900]
      {M₁ M₂ : LeftModule R} (φ : M₁ →lm M₂) : is_module_hom R φ :=
  homomorphism.p φ

  section

    variable (φ : M₁ →lm M₂)

    definition to_respect_add (x y : M₁) : φ (x + y) = φ x + φ y :=
    respect_add φ x y

    definition to_respect_smul (a : R) (x : M₁) : φ (a • x) = a • (φ x) :=
    respect_smul R φ a x

    definition to_respect_sub (x y : M₁) : φ (x - y) = φ x - φ y :=
    respect_sub φ x y

    definition is_embedding_of_homomorphism (* φ -/ (H : Π{x}, φ x = 0 → x = 0) : is_embedding φ :=
    is_embedding_of_is_add_hom φ @H

    variables (M₁ M₂)
    definition is_set_homomorphism [instance] : is_set (M₁ →lm M₂) :=
    begin
      have H : M₁ →lm M₂ ≃ Σ(f : LeftModule.carrier M₁ → LeftModule.carrier M₂),
        is_module_hom (Ring.carrier R) f,
      begin
        fapply equiv.MK,
        { intro φ, induction φ, constructor, exact p},
        { intro v, induction v with f H, constructor, exact H},
        { intro v, induction v, reflexivity},
        { intro φ, induction φ, reflexivity}
      end,
    have ∀ f : LeftModule.carrier M₁ → LeftModule.carrier M₂,
      is_set (is_module_hom (Ring.carrier R) f), from _,
    exact is_trunc_equiv_closed_rev _ H _
  end

  variables {M₁ M₂}
  definition pmap_of_homomorphism [constructor] (* φ -/ :
    pSet_of_LeftModule M₁ →* pSet_of_LeftModule M₂ :=
  have H : φ 0 = 0, from respect_zero φ,
  pmap.mk φ begin esimp, exact H end

  definition homomorphism_change_fun [constructor]
    (φ : M₁ →lm M₂) (f : M₁ → M₂) (p : φ ~ f) : M₁ →lm M₂ :=
  homomorphism.mk f
    (prod.mk
      (λx₁ x₂, (p (x₁ + x₂))⁻¹ ⬝ to_respect_add φ x₁ x₂ ⬝ ap011 _ (p x₁) (p x₂))
      (λ a x, (p (a • x))⁻¹ ⬝ to_respect_smul φ a x ⬝ ap01 _ (p x)))

  definition homomorphism_eq (φ₁ φ₂ : M₁ →lm M₂) (p : φ₁ ~ φ₂) : φ₁ = φ₂ :=
  begin
    induction φ₁ with φ₁ q₁, induction φ₂ with φ₂ q₂, esimp at p, induction p,
    exact ap (homomorphism.mk φ₁) !is_prop.elim
  end

  end

  section

  definition homomorphism.mk' [constructor] (φ : M₁ → M₂)
    (p : Π(g₁ g₂ : M₁), φ (g₁ + g₂) = φ g₁ + φ g₂)
    (q : Π(r : R) x, φ (r • x) = r • φ x) : M₁ →lm M₂ :=
  homomorphism.mk φ (p, q)

  definition to_respect_zero (φ : M₁ →lm M₂) : φ 0 = 0 :=
  respect_zero φ

  definition homomorphism_compose [reducible] [constructor] (f' : M₂ →lm M₃) (f : M₁ →lm M₂) :
    M₁ →lm M₃ :=
  homomorphism.mk (f' ∘ f) !is_module_hom_comp

  variable (M)
  definition homomorphism_id [reducible] [constructor] [refl] : M →lm M :=
  homomorphism.mk (@id M) !is_module_hom_id
  variable {M}

  abbreviation lmid [constructor] := homomorphism_id M
  infixr ` ∘lm `:75 := homomorphism_compose

  definition lm_constant [constructor] (M₁ M₂ : LeftModule R) : M₁ →lm M₂ :=
  homomorphism.mk (const M₁ 0) !is_module_hom_constant

  definition trivial_image_of_is_contr {R} {M₁ M₂ : LeftModule R} {φ : M₁ →lm M₂} (H : is_contr M₁)
    ⦃m : M₂⦄ (hm : image φ m) : m = 0 :=
  begin
    induction hm with m' p, induction p,
    exact ap φ (@eq_of_is_contr _ H _ _) ⬝ to_respect_zero φ
  end

  structure isomorphism (M₁ M₂ : LeftModule R) :=
    (to_hom : M₁ →lm M₂)
    (is_equiv_to_hom : is_equiv to_hom)

  infix ` ≃lm `:25 := isomorphism
  attribute isomorphism.to_hom [coercion]
  attribute isomorphism.is_equiv_to_hom [instance]
  attribute isomorphism._trans_of_to_hom [unfold 4]

  definition equiv_of_isomorphism [constructor] (φ : M₁ ≃lm M₂) : M₁ ≃ M₂ :=
  equiv.mk φ !isomorphism.is_equiv_to_hom

  section
  local attribute pSet_of_LeftModule [coercion]
  definition pequiv_of_isomorphism [constructor] (φ : M₁ ≃lm M₂) : M₁ ≃* M₂ :=
  pequiv_of_equiv (equiv_of_isomorphism φ) (to_respect_zero φ)
  end

  definition isomorphism_of_equiv [constructor] (φ : M₁ ≃ M₂)
    (p : Π(g₁ g₂ : M₁), φ (g₁ + g₂) = φ g₁ + φ g₂)
    (q : Πr x, φ (r • x) = r • φ x) : M₁ ≃lm M₂ :=
  isomorphism.mk (homomorphism.mk φ (p, q)) !to_is_equiv

  definition isomorphism_of_eq [constructor] {M₁ M₂ : LeftModule R} (p : M₁ = M₂ :> LeftModule R)
    : M₁ ≃lm M₂ :=
  isomorphism_of_equiv (equiv_of_eq (ap LeftModule.carrier p))
    begin intros, induction p, reflexivity end
    begin intros, induction p, reflexivity end

  -- definition pequiv_of_isomorphism_of_eq {M₁ M₂ : LeftModule R} (p : M₁ = M₂ :> LeftModule R) :
  --   pequiv_of_isomorphism (isomorphism_of_eq p) = pequiv_of_eq (ap pType_of_LeftModule p) :=
  -- begin
  --   induction p,
  --   apply pequiv_eq,
  --   fapply pmap_eq,
  --   { intro g, reflexivity},
  --   { apply is_prop.elim}
  -- end

  definition to_lminv [constructor] (φ : M₁ ≃lm M₂) : M₂ →lm M₁ :=
  homomorphism.mk φ⁻¹
    abstract begin
    split,
      intro g₁ g₂, apply inj' φ,
      rewrite [respect_add φ, +right_inv φ],
      intro r x, apply inj' φ,
      rewrite [to_respect_smul φ, +right_inv φ],
    end end

  variable (M)
  definition isomorphism.refl [refl] [constructor] : M ≃lm M :=
  isomorphism.mk lmid !is_equiv_id
  variable {M}

  definition isomorphism.rfl [refl] [constructor] : M ≃lm M := isomorphism.refl M

  definition isomorphism.symm [symm] [constructor] (φ : M₁ ≃lm M₂) : M₂ ≃lm M₁ :=
  isomorphism.mk (to_lminv φ) !is_equiv_inv

  definition isomorphism.trans [trans] [constructor] (φ : M₁ ≃lm M₂) (ψ : M₂ ≃lm M₃) : M₁ ≃lm M₃ :=
  isomorphism.mk (ψ ∘lm φ) (is_equiv_compose ψ φ _ _)

  definition isomorphism.eq_trans [trans] [constructor]
     {M₁ M₂ : LeftModule R} {M₃ : LeftModule R} (φ : M₁ = M₂) (ψ : M₂ ≃lm M₃) : M₁ ≃lm M₃ :=
  proof isomorphism.trans (isomorphism_of_eq φ) ψ qed

  definition isomorphism.trans_eq [trans] [constructor]
    {M₁ : LeftModule R} {M₂ M₃ : LeftModule R} (φ : M₁ ≃lm M₂) (ψ : M₂ = M₃) : M₁ ≃lm M₃ :=
  isomorphism.trans φ (isomorphism_of_eq ψ)

  postfix `⁻¹ˡᵐ`:(max + 1) := isomorphism.symm
  infixl ` ⬝lm `:75 := isomorphism.trans
  infixl ` ⬝lmp `:75 := isomorphism.trans_eq
  infixl ` ⬝plm `:75 := isomorphism.eq_trans

  definition homomorphism_of_eq [constructor] {M₁ M₂ : LeftModule R} (p : M₁ = M₂ :> LeftModule R)
    : M₁ →lm M₂ :=
  isomorphism_of_eq p

  definition group_homomorphism_of_lm_homomorphism [constructor] {M₁ M₂ : LeftModule R}
    (φ : M₁ →lm M₂) : M₁ →a M₂ :=
  add_homomorphism.mk φ (to_respect_add φ)

  definition lm_homomorphism_of_group_homomorphism [constructor] {M₁ M₂ : LeftModule R}
    (φ : M₁ →a M₂) (h : Π(r : R) g, φ (r • g) = r • φ g) : M₁ →lm M₂ :=
  homomorphism.mk' φ (group.to_respect_add φ) h

  definition group_isomorphism_of_lm_isomorphism [constructor] {M₁ M₂ : LeftModule R}
    (φ : M₁ ≃lm M₂) : AddGroup_of_AddAbGroup M₁ ≃g AddGroup_of_AddAbGroup M₂ :=
  group.isomorphism.mk (group_homomorphism_of_lm_homomorphism φ) (isomorphism.is_equiv_to_hom φ)

  definition lm_isomorphism_of_group_isomorphism [constructor] {M₁ M₂ : LeftModule R}
    (φ : AddGroup_of_AddAbGroup M₁ ≃g AddGroup_of_AddAbGroup M₂)
    (h : Π(r : R) g, φ (r • g) = r • φ g) : M₁ ≃lm M₂ :=
  isomorphism.mk (lm_homomorphism_of_group_homomorphism φ h) (group.isomorphism.is_equiv_to_hom φ)

  definition trivial_homomorphism [constructor] (M₁ M₂ : LeftModule R) : M₁ →lm M₂ :=
  lm_homomorphism_of_group_homomorphism (group.trivial_add_homomorphism M₁ M₂)
    (λs m, (smul_zero s)⁻¹)


  section
  local attribute pSet_of_LeftModule [coercion]
  definition is_exact_mod (f : M₁ →lm M₂) (f' : M₂ →lm M₃) : Type :=
  @is_exact M₁ M₂ M₃ (homomorphism_fn f) (homomorphism_fn f')

  definition is_exact_mod.mk {f : M₁ →lm M₂} {f' : M₂ →lm M₃}
    (h₁ : Πm, f' (f m) = 0) (h₂ : Πm, f' m = 0 → image f m) : is_exact_mod f f' :=
  is_exact.mk h₁ h₂

  structure short_exact_mod (A B C : LeftModule R) :=
    (f : A →lm B)
    (g : B →lm C)
    (h : @is_short_exact A B C f g)

  structure five_exact_mod (A B C D E : LeftModule R) :=
    (f₁ : A →lm B)
    (f₂ : B →lm C)
    (f₃ : C →lm D)
    (f₄ : D →lm E)
    (h₁ : @is_exact A B C f₁ f₂)
    (h₂ : @is_exact B C D f₂ f₃)
    (h₃ : @is_exact C D E f₃ f₄)

  local abbreviation g_of_lm := @group_homomorphism_of_lm_homomorphism
  definition short_exact_mod_of_is_exact {X A B C Y : LeftModule R}
    (k : X →lm A) (f : A →lm B) (g : B →lm C) (l : C →lm Y)
    (hX : is_contr X) (hY : is_contr Y)
    (kf : is_exact_mod k f) (fg : is_exact_mod f g) (gl : is_exact_mod g l) :
    short_exact_mod A B C :=
  short_exact_mod.mk f g
    (is_short_exact_of_is_exact (g_of_lm k) (g_of_lm f) (g_of_lm g) (g_of_lm l) hX hY kf fg gl)

  definition short_exact_mod_isomorphism {A B A' B' C C' : LeftModule R}
    (eA : A ≃lm A') (eB : B ≃lm B') (eC : C ≃lm C')
    (H : short_exact_mod A' B' C') : short_exact_mod A B C :=
  short_exact_mod.mk (eB⁻¹ˡᵐ ∘lm short_exact_mod.f H ∘lm eA) (eC⁻¹ˡᵐ ∘lm short_exact_mod.g H ∘lm eB)
    (is_short_exact_equiv _ _
      (equiv_of_isomorphism eA) (equiv_of_isomorphism eB) (pequiv_of_isomorphism eC)
      (λa, to_right_inv (equiv_of_isomorphism eB) _) (λb, to_right_inv (equiv_of_isomorphism eC) _)
      (short_exact_mod.h H))

  definition is_contr_middle_of_short_exact_mod {A B C : LeftModule R} (H : short_exact_mod A B C)
    (HA : is_contr A) (HC : is_contr C) : is_contr B :=
  is_contr_middle_of_is_exact (is_exact_of_is_short_exact (short_exact_mod.h H))

  definition is_contr_right_of_short_exact_mod {A B C : LeftModule R} (H : short_exact_mod A B C)
    (HB : is_contr B) : is_contr C :=
  is_contr_right_of_is_short_exact (short_exact_mod.h H) _ _

  definition is_contr_left_of_short_exact_mod {A B C : LeftModule R} (H : short_exact_mod A B C)
    (HB : is_contr B) : is_contr A :=
  is_contr_left_of_is_short_exact (short_exact_mod.h H) _ pt

  definition isomorphism_of_is_contr_left {A B C : LeftModule R} (H : short_exact_mod A B C)
    (HA : is_contr A) : B ≃lm C :=
  isomorphism.mk (short_exact_mod.g H)
    begin
      apply @is_equiv_right_of_is_short_exact _ _ _
        (group_homomorphism_of_lm_homomorphism (short_exact_mod.f H))
        (group_homomorphism_of_lm_homomorphism (short_exact_mod.g H)),
      rexact short_exact_mod.h H, exact HA,
    end

  definition isomorphism_of_is_contr_right {A B C : LeftModule R} (H : short_exact_mod A B C)
    (HC : is_contr C) : A ≃lm B :=
  isomorphism.mk (short_exact_mod.f H)
    begin
      apply @is_equiv_left_of_is_short_exact _ _ _
        (group_homomorphism_of_lm_homomorphism (short_exact_mod.f H))
        (group_homomorphism_of_lm_homomorphism (short_exact_mod.g H)),
      rexact short_exact_mod.h H, exact HC,
    end

  end

  end

end

  (* we say that an left module D is built from the sequence E if
     D is a "twisted sum" of the E, and E has only finitely many nontrivial values -/
  open nat
  structure is_built_from.{u v w} {R : Ring} (D : LeftModule.{u v} R)
      (E : ℕ → LeftModule.{u w} R) : Type.{max u (v+1) w} :=
    (part : ℕ → LeftModule.{u v} R)
    (ses : Πn, short_exact_mod (E n) (part n) (part (n+1)))
    (e0 : part 0 ≃lm D)
    (n₀ : ℕ)
    (HD' : Π(s : ℕ), n₀ ≤ s → is_contr (part s))

  open is_built_from
  universe variables u v w
  variables {R : Ring.{u}} {D D' : LeftModule.{u v} R} {E E' : ℕ → LeftModule.{u w} R}

  definition is_built_from_shift (H : is_built_from D E) :
    is_built_from (part H 1) (λn, E (n+1)) :=
  is_built_from.mk (λn, part H (n+1)) (λn, ses H (n+1)) isomorphism.rfl (pred (n₀ H))
    (λs Hle, HD' H _ (le_succ_of_pred_le Hle))

  definition is_built_from_isomorphism (e : D ≃lm D') (f : Πn, E n ≃lm E' n)
    (H : is_built_from D E) : is_built_from D' E' :=
  ⦃is_built_from, H, e0 := e0 H ⬝lm e,
    ses := λn, short_exact_mod_isomorphism (f n)⁻¹ˡᵐ isomorphism.rfl isomorphism.rfl (ses H n)⦄

  definition is_built_from_isomorphism_left (e : D ≃lm D') (H : is_built_from D E) :
    is_built_from D' E :=
  ⦃is_built_from, H, e0 := e0 H ⬝lm e⦄

  definition isomorphism_of_is_contr_submodule (H : is_built_from D E) (n : ℕ)
    (HE : is_contr (E n)) : part H n ≃lm part H (n+1) :=
  isomorphism_of_is_contr_left (ses H n) HE

  definition isomorphism_of_is_contr_submodules_range (H : is_built_from D E) {n k : ℕ}
  (Hnk : n ≤ k) (HE : Πl, n ≤ l → l < k → is_contr (E l)) : part H n ≃lm part H k :=
  begin
    induction Hnk with k Hnk IH,
    { reflexivity },
    { refine IH (λl Hnl Hlk, HE l Hnl (lt.step Hlk)) ⬝lm
             isomorphism_of_is_contr_submodule H k (HE k Hnk !self_lt_succ), }
  end

  definition is_contr_quotients_of_is_contr_total (H : is_built_from D E) (HD : is_contr D) (n : ℕ) :
    is_contr (part H n) :=
  begin
    induction n with n IH,
    { exact is_trunc_equiv_closed_rev -2 (equiv_of_isomorphism (e0 H)) _ },
    { exact is_contr_right_of_short_exact_mod (ses H n) IH }
  end

  definition is_contr_quotients_of_is_contr_submodules (H : is_built_from D E) {n : ℕ}
    (HE : Πk, n ≤ k → is_contr (E k)) : is_contr (part H n) :=
  begin
    refine is_contr_equiv_closed_rev _ (HD' H (max n (n₀ H)) !le_max_right),
    apply equiv_of_isomorphism,
    apply isomorphism_of_is_contr_submodules_range H !le_max_left,
    intros l Hnl Hl', exact HE l Hnl
  end
  (* alternate direct proof -/
  -- nat.rec_down (λk, is_contr (part H (n + k))) _ (HD' H _ !nat.le_add_left)
  --   (λk H2, is_contr_middle_of_short_exact_mod (ses H (n + k)) (HE (n + k) !nat.le_add_right)
  --     proof H2 qed)

  definition isomorphism_of_is_contr_submodules (H : is_built_from D E) {n : ℕ}
    (HE : Πk, n < k → is_contr (E k)) : E n ≃lm part H n :=
  isomorphism_of_is_contr_right (ses H n) (is_contr_quotients_of_is_contr_submodules H HE)

  -- definition is_contr_quotients_of_is_contr_submodules1 (H : is_built_from D E) (n : ℕ)
  --   (HE : Πk, n ≤ k → is_contr (E k)) : is_contr (part H n) :=
  -- nat.rec_down (λk, is_contr (part H (n + k))) _ (HD' H _ !nat.le_add_left)
  --   (λk H2, is_contr_middle_of_short_exact_mod (ses H (n + k)) (HE (n + k) !nat.le_add_right)
  --     proof H2 qed)

  definition isomorphism_zero_of_is_built_from (H : is_built_from D E) (p : n₀ H = 1) : E 0 ≃lm D :=
  isomorphism_of_is_contr_right (ses H 0) (HD' H 1 (le_of_eq p)) ⬝lm e0 H

  definition isomorphism_total_of_is_contr_submodules (H : is_built_from D E) {n : ℕ}
    (HE : Πk, k < n → is_contr (E k)) : D ≃lm part H n :=
  (e0 H)⁻¹ˡᵐ ⬝lm isomorphism_of_is_contr_submodules_range H !zero_le (λk H0k Hkn, HE k Hkn)

  definition isomorphism_of_is_contr_submodules_but_one (H : is_built_from D E) {n : ℕ}
    (HE : Πk, k ≠ n → is_contr (E k)) : D ≃lm E n :=
  (e0 H)⁻¹ˡᵐ ⬝lm
  isomorphism_of_is_contr_submodules_range H !zero_le (λk H0k Hkn, HE k (ne_of_lt Hkn)) ⬝lm
  (isomorphism_of_is_contr_submodules H (λk Hk, HE k (ne.symm (ne_of_lt Hk))))⁻¹ˡᵐ

  definition short_exact_mod_of_is_contr_submodules (H : is_built_from D E) {n m : ℕ} (Hnm : n < m)
    (HE : Πk, k ≠ n → k ≠ m → is_contr (E k)) : short_exact_mod (E n) D (E m) :=
  begin
    refine short_exact_mod_isomorphism isomorphism.rfl _ _ (ses H n),
    { exact isomorphism_total_of_is_contr_submodules H (λk Hk, HE k (ne_of_lt Hk)
              (ne_of_lt (lt.trans Hk Hnm))) },
    { exact isomorphism_of_is_contr_submodules H
              (λk Hk, HE k (ne.symm (ne_of_lt (lt.trans Hnm Hk))) (ne.symm (ne_of_lt Hk))) ⬝lm
            (isomorphism_of_is_contr_submodules_range H Hnm
              (λk Hnk Hkm, HE k (ne.symm (ne_of_lt Hnk)) (ne_of_lt Hkm)))⁻¹ˡᵐ }
  end

  definition is_contr_submodules (H : is_built_from D E) (HD : is_contr D) (n : ℕ) :
    is_contr (E n) :=
  begin
    apply is_contr_left_of_short_exact_mod (ses H n),
    exact is_contr_quotients_of_is_contr_total H HD n
  end

  definition is_contr_total (H : is_built_from D E) (HE : Πn, is_contr (E n)) : is_contr D :=
  have is_contr (part H 0), from is_contr_quotients_of_is_contr_submodules H (λn H, HE n),
  is_contr_equiv_closed (equiv_of_isomorphism (e0 H)) _

section int
open int
definition left_module_int_of_ab_group [constructor] (A : Type) [add_ab_group A] : left_module rℤ A :=
left_module_of_ab_group imul imul_add add_imul mul_imul one_imul

definition LeftModule_int_of_AbGroup [constructor] (A : AddAbGroup) : LeftModule rℤ :=
LeftModule.mk A (left_module_int_of_ab_group A)

definition lm_hom_int.mk [constructor] {A B : AbGroup} (φ : A →g B) :
  LeftModule_int_of_AbGroup A →lm LeftModule_int_of_AbGroup B :=
lm_homomorphism_of_group_homomorphism φ (to_respect_imul φ)

definition lm_iso_int.mk [constructor] {A B : AbGroup} (φ : A ≃g B) :
  LeftModule_int_of_AbGroup A ≃lm LeftModule_int_of_AbGroup B :=
isomorphism.mk (lm_hom_int.mk φ) (group.isomorphism.is_equiv_to_hom φ)

definition group_isomorphism_of_lm_isomorphism_int [constructor] {A B : AbGroup}
  (φ : LeftModule_int_of_AbGroup A ≃lm LeftModule_int_of_AbGroup B) : A ≃g B :=
group_isomorphism_of_lm_isomorphism φ

end int


end left_module
