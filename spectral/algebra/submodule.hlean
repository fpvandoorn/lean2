(* submodules and quotient modules *)

import .left_module .quotient_group .module_chain_complex

open algebra eq group sigma sigma.ops is_trunc function trunc equiv is_equiv property
universe variable u
namespace left_module
(* submodules *)
variables {R : Ring} {M M₁ M₁' M₂ M₂' M₃ M₃' : LeftModule R} {m m₁ m₂ : M}

structure is_submodule [class] (M : LeftModule R) (S : property M) : Type.
  (zero_mem : 0 ∈ S)
  (add_mem : forall (g h), g ∈ S -> h ∈ S -> g + h ∈ S)
  (smul_mem : forall (g) (r : R), g ∈ S -> r • g ∈ S)

Definition zero_mem {R : Ring} {M : LeftModule R} (S : property M) [is_submodule M S] . is_submodule.zero_mem S
Definition add_mem {R : Ring} {M : LeftModule R} (S : property M) [is_submodule M S] . @is_submodule.add_mem R M S
Definition smul_mem {R : Ring} {M : LeftModule R} (S : property M) [is_submodule M S] . @is_submodule.smul_mem R M S

Definition neg_mem (S : property M) [is_submodule M S] (m) (H : m ∈ S) : -m ∈ S.
transport (fun x => x ∈ S) (neg_one_smul m) (smul_mem S (- 1) H)

Definition is_normal_submodule (S : property M) [is_submodule M S] (m₁ m₂) (H : S m₁) : S (m₂ + m₁ + (-m₂)).
transport (fun x => S x) (by rewrite [add.comm, neg_add_cancel_left]) H


variables {S : property M} [is_submodule M S] {S₂ : property M₂} [is_submodule M₂ S₂]

Definition is_subgroup_of_is_submodule [instance] (S : property M) [is_submodule M S] :
  is_subgroup (AddGroup_of_AddAbGroup M) S.
is_subgroup.mk (zero_mem S) (add_mem S) (neg_mem S)

Definition is_subgroup_of_is_submodule' [instance] (S : property M) [is_submodule M S] : is_subgroup (Group_of_AbGroup (AddAbGroup_of_LeftModule M)) S.
is_subgroup.mk (zero_mem S) (add_mem S) (neg_mem S)

Definition submodule' (S : property M) [is_submodule M S] : AddAbGroup.
ab_subgroup S
Definition submodule_smul (S : property M) [is_submodule M S] (r : R) :
  submodule' S ->a submodule' S.
ab_subgroup_functor (smul_homomorphism M r) (fun g => smul_mem S r)

Definition submodule_smul_right_distrib (r s : R) (n : submodule' S) :
  submodule_smul S (r + s) n = submodule_smul S r n + submodule_smul S s n.
Proof.
  refine subgroup_functor_homotopy _ _ _ n @ !subgroup_functor_mul^-1ᵖ =>
  intro m, exact to_smul_right_distrib r s m
Defined.

Definition submodule_mul_smul' (r s : R) (n : submodule' S) :
  submodule_smul S (r * s) n = (submodule_smul S r og submodule_smul S s) n.
Proof.
  refine subgroup_functor_homotopy _ _ _ n @ (subgroup_functor_compose _ _ _ _ n)^-1ᵖ =>
  intro m, exact to_mul_smul r s m
Defined.

Definition submodule_mul_smul (r s : R) (n : submodule' S) :
  submodule_smul S (r * s) n = submodule_smul S r (submodule_smul S s n).
by rexact submodule_mul_smul' r s n

Definition submodule_one_smul (n : submodule' S) : submodule_smul S (1 : R) n = n.
Proof.
  refine subgroup_functor_homotopy _ _ _ n @ !subgroup_functor_gid =>
  intro m, exact to_one_smul m
Defined.

Definition submodule (S : property M) [is_submodule M S] : LeftModule R.
LeftModule_of_AddAbGroup (submodule' S) (submodule_smul S)
  (fun r => homomorphism.addstruct (submodule_smul S r))
  submodule_smul_right_distrib
  submodule_mul_smul
  submodule_one_smul

Definition submodule_incl (S : property M) [is_submodule M S] : submodule S ->lm M.
lm_homomorphism_of_group_homomorphism (incl_of_subgroup _)
Proof.
  intro r m, induction m with m hm, reflexivity
Defined.

Definition hom_lift {K : property M₂} [is_submodule M₂ K] (φ : M₁ ->lm M₂)
  (h : forall (m : M₁), φ m ∈ K) : M₁ ->lm submodule K.
lm_homomorphism_of_group_homomorphism (hom_lift (group_homomorphism_of_lm_homomorphism φ) _ h)
Proof.
  intro r g, exact subtype_eq (to_respect_smul φ r g)
Defined.

Definition submodule_functor {S : property M₁} [is_submodule M₁ S]
  {K : property M₂} [is_submodule M₂ K]
  (φ : M₁ ->lm M₂) (h : forall (m : M₁), m ∈ S -> φ m ∈ K) : submodule S ->lm submodule K.
hom_lift (φ olm submodule_incl S) (by intro m; exact h m.1 m.2)

Definition hom_lift_compose {K : property M₃} [is_submodule M₃ K]
  (φ : M₂ ->lm M₃) (h : forall (m : M₂), φ m ∈ K) (ψ : M₁ ->lm M₂) :
  hom_lift φ h olm ψ == hom_lift (φ olm ψ) proof (fun m => h (ψ m)) qed.
by reflexivity

Definition hom_lift_homotopy {K : property M₂} [is_submodule M₂ K] {φ : M₁ ->lm M₂}
  {h : forall (m : M₁), φ m ∈ K} {φ' : M₁ ->lm M₂}
  {h' : forall (m : M₁), φ' m ∈ K} (p : φ == φ') : hom_lift φ h == hom_lift φ' h'.
fun g => subtype_eq (p g)

Definition incl_smul (S : property M) [is_submodule M S] (r : R) (m : M) (h : S m) :
  r • ⟨m, h⟩ = ⟨_, smul_mem S r h⟩ :> submodule S.
by reflexivity

Definition property_submodule (S₁ S₂ : property M) [is_submodule M S₁] [is_submodule M S₂] :
  property (submodule S₁) . {m | submodule_incl S₁ m ∈ S₂}

Definition is_submodule_property_submodule [instance] (S₁ S₂ : property M) [is_submodule M S₁] [is_submodule M S₂] :
  is_submodule (submodule S₁) (property_submodule S₁ S₂).
is_submodule.mk
  (mem_property_of (zero_mem S₂))
  (fun m n p q => mem_property_of (add_mem S₂ (of_mem_property_of p) (of_mem_property_of q)))
Proof.
  intro m r p, induction m with m hm, apply mem_property_of,
  apply smul_mem S₂, exact (of_mem_property_of p)
Defined.

Definition eq_zero_of_mem_property_submodule_trivial {S₁ S₂ : property M} [is_submodule M S₁] [is_submodule M S₂]
  (h : forall (m), m ∈ S₂ -> m = 0) (m : submodule S₁) (Sm : m ∈ property_submodule S₁ S₂) : m = 0.
Proof.
  fapply subtype_eq,
  apply h (of_mem_property_of Sm)
Defined.

Definition is_contr_submodule (S : property M) [is_submodule M S] (H : is_contr M) :
  is_contr (submodule S).
have is_prop M, from _,
have is_prop (submodule S), from @is_trunc_sigma _ _ _ this _,
is_contr_of_inhabited_prop 0 this

Definition submodule_isomorphism (S : property M) [is_submodule M S] (h : forall g, g ∈ S) :
  submodule S <~>lm M.
isomorphism.mk (submodule_incl S) (is_equiv_incl_of_subgroup S h)

Definition submodule_isomorphism_submodule {S : property M₁} [is_submodule M₁ S]
  {K : property M₂} [is_submodule M₂ K]
  (φ : M₁ <~>lm M₂) (h : forall (m : M₁), m ∈ S ↔ φ m ∈ K) : submodule S <~>lm submodule K.
lm_isomorphism_of_group_isomorphism
  (subgroup_isomorphism_subgroup (group_isomorphism_of_lm_isomorphism φ) h)
  (by rexact to_respect_smul (submodule_functor φ (fun g => iff.mp (h g))))

(* quotient modules *)

Definition quotient_module' (S : property M) [is_submodule M S] : AddAbGroup.
quotient_ab_group S
Definition quotient_module_smul (S : property M) [is_submodule M S] (r : R) :
  quotient_module' S ->a quotient_module' S.
quotient_ab_group_functor (smul_homomorphism M r) (fun g => smul_mem S r)

Definition quotient_module_smul_right_distrib (r s : R) (n : quotient_module' S) :
  quotient_module_smul S (r + s) n = quotient_module_smul S r n + quotient_module_smul S s n.
Proof.
  refine quotient_ab_group_functor_homotopy _ _ _ n @ !quotient_ab_group_functor_mul^-1 =>
  intro m, exact to_smul_right_distrib r s m
Defined.

Definition quotient_module_mul_smul' (r s : R) (n : quotient_module' S) :
  quotient_module_smul S (r * s) n = (quotient_module_smul S r og quotient_module_smul S s) n.
Proof.
  apply eq.symm,
  apply eq.trans (quotient_ab_group_functor_compose _ _ _ _ n) =>
  apply quotient_ab_group_functor_homotopy =>
  intro m, exact eq.symm (to_mul_smul r s m)
Defined.

Definition quotient_module_mul_smul (r s : R) (n : quotient_module' S) :
  quotient_module_smul S (r * s) n = quotient_module_smul S r (quotient_module_smul S s n).
by rexact quotient_module_mul_smul' r s n

Definition quotient_module_one_smul (n : quotient_module' S) : quotient_module_smul S (1 : R) n = n.
Proof.
  refine quotient_ab_group_functor_homotopy _ _ _ n @ !quotient_ab_group_functor_gid =>
  intro m, exact to_one_smul m
Defined.

variable (S)
Definition quotient_module (S : property M) [is_submodule M S] : LeftModule R.
LeftModule_of_AddAbGroup (quotient_module' S) (quotient_module_smul S)
  (fun r => homomorphism.addstruct (quotient_module_smul S r))
  quotient_module_smul_right_distrib
  quotient_module_mul_smul
  quotient_module_one_smul

Definition quotient_map : M ->lm quotient_module S.
lm_homomorphism_of_group_homomorphism (ab_qg_map _) (fun r g => idp)

Definition quotient_map_eq_zero (m : M) (H : S m) : quotient_map S m = 0.
@ab_qg_map_eq_one _ _ _ _ H

Definition rel_of_quotient_map_eq_zero (m : M) (H : quotient_map S m = 0) : S m.
@rel_of_qg_map_eq_one _ _ _ m H

variable {S}
Definition respect_smul_quotient_elim (φ : M ->lm M₂) (H : forall (m), m ∈ S -> φ m = 0)
  (r : R) (m : quotient_module S) :
  quotient_ab_group_elim (group_homomorphism_of_lm_homomorphism φ) H
  (@has_scalar.smul _ (quotient_module S) _ r m) =
  r • quotient_ab_group_elim (group_homomorphism_of_lm_homomorphism φ) H m.
Proof.
  revert m,
  refine @set_quotient.rec_prop _ _ _ (fun x => !is_trunc_eq) _,
  intro m,
  exact to_respect_smul φ r m
Defined.

Definition quotient_elim (φ : M ->lm M₂) (H : forall (m), m ∈ S -> φ m = 0) :
  quotient_module S ->lm M₂.
lm_homomorphism_of_group_homomorphism
  (quotient_ab_group_elim (group_homomorphism_of_lm_homomorphism φ) H)
  (respect_smul_quotient_elim φ H)

Definition is_prop_quotient_module (S : property M) [is_submodule M S] [H : is_prop M] : is_prop (quotient_module S).
Proof. apply @set_quotient.is_trunc_set_quotient, exact H end

Definition is_contr_quotient_module [instance] (S : property M) [is_submodule M S]
  (H : is_contr M) : is_contr (quotient_module S).
have is_prop M, from _,
have is_prop (quotient_module S), from @set_quotient.is_trunc_set_quotient _ _ _ this,
is_contr_of_inhabited_prop 0 this

Definition rel_of_is_contr_quotient_module (S : property M) [is_submodule M S]
  (H : is_contr (quotient_module S)) (m : M) : S m.
rel_of_quotient_map_eq_zero S m (@eq_of_is_contr _ H _ _)

Definition quotient_module_isomorphism (S : property M) [is_submodule M S] (h : forall (m), S m -> m = 0) :
  quotient_module S <~>lm M.
(isomorphism.mk (quotient_map S) (is_equiv_ab_qg_map S h))^-1ˡᵐ

Definition quotient_module_functor (φ : M ->lm M₂) (h : forall , g ∈ S -> φ g ∈ S₂) :
  quotient_module S ->lm quotient_module S₂.
quotient_elim (quotient_map S₂ olm φ)
Proof. intros m Hm, rexact quotient_map_eq_zero S₂ (φ m) (h m Hm) end

Definition quotient_module_isomorphism_quotient_module (φ : M <~>lm M₂)
  (h : forall m, m ∈ S ↔ φ m ∈ S₂) : quotient_module S <~>lm quotient_module S₂.
lm_isomorphism_of_group_isomorphism
  (quotient_ab_group_isomorphism_quotient_ab_group (group_isomorphism_of_lm_isomorphism φ) h)
  (to_respect_smul (quotient_module_functor φ (fun g => iff.mp (h g))))

(* specific submodules *)
Definition has_scalar_image (φ : M₁ ->lm M₂) (m : M₂) (r : R)
  (h : image φ m) : image φ (r • m).
Proof.
  induction h with m' p,
  apply image.mk (r • m'),
  refine to_respect_smul φ r m' @ ap (fun x => r • x) p,
Defined.

Definition is_submodule_image [instance] (φ : M₁ ->lm M₂) : is_submodule M₂ (image φ).
is_submodule.mk
  (show 0 ∈ image (group_homomorphism_of_lm_homomorphism φ),
Proof. apply is_subgroup.one_mem, apply is_subgroup_image end)
  (fun g₁ g₂ hg₁ hg₂ =>
  show g₁ + g₂ ∈ image (group_homomorphism_of_lm_homomorphism φ),
Proof.
  apply @is_subgroup.mul_mem,
  apply is_subgroup_image, exact hg₁, exact hg₂
Defined.)
  (has_scalar_image φ)

(*
Definition image_rel (φ : M₁ ->lm M₂) : submodule_rel M₂.
submodule_rel_of_subgroup_rel
  (image_subgroup (group_homomorphism_of_lm_homomorphism φ))
  (has_scalar_image φ)
*)

Definition image_trivial (φ : M₁ ->lm M₂) [H : is_contr M₁] (m : M₂) (h : m ∈ image φ) : m = 0.
Proof.
  refine image.rec _ h,
  intro x p,
  refine p^-1 @ ap φ _ @ to_respect_zero φ,
  apply @is_prop.elim, apply is_trunc_succ, exact H
Defined.

Definition image_module (φ : M₁ ->lm M₂) : LeftModule R . submodule (image φ)


Definition image_lift (φ : M₁ ->lm M₂) : M₁ ->lm image_module φ.
hom_lift φ (fun m => image.mk m idp)

Definition is_surjective_image_lift (φ : M₁ ->lm M₂) : is_surjective (image_lift φ).
Proof.
  refine total_image.rec _, intro m, exact image.mk m (subtype_eq idp)
Defined.

variables {ψ : M₂ ->lm M₃} {φ : M₁ ->lm M₂} {θ : M₁ ->lm M₃} {ψ' : M₂' ->lm M₃'} {φ' : M₁' ->lm M₂'}

Definition image_elim (θ : M₁ ->lm M₃) (h : forall (g), φ g = 0 -> θ g = 0) :
  image_module φ ->lm M₃.
Proof.
  fapply homomorphism.mk,
  change Image (group_homomorphism_of_lm_homomorphism φ) -> M₃,
  exact image_elim (group_homomorphism_of_lm_homomorphism θ) h,
  split,
  { exact homomorphism.struct (image_elim (group_homomorphism_of_lm_homomorphism θ) _) },
  { intro r, refine @total_image.rec _ _ _ _ (fun x => !is_trunc_eq) _, intro g,
  apply to_respect_smul }
Defined.

Definition image_elim_compute (h : forall (g), φ g = 0 -> θ g = 0) :
  image_elim θ h olm image_lift φ == θ.
Proof.
  reflexivity
Defined.


Definition is_contr_image_module [instance] (φ : M₁ ->lm M₂) (H : is_contr M₂) :
  is_contr (image_module φ).
is_contr_submodule _ _

Definition is_contr_image_module_of_is_contr_dom (φ : M₁ ->lm M₂) (H : is_contr M₁) :
  is_contr (image_module φ).
is_contr.mk 0
Proof.
  have forall (x : image_module φ), is_prop (0 = x), from _,
  apply @total_image.rec,
  exact this,
  intro m,
  have h : is_contr (LeftModule.carrier M₁), from H,
  induction (eq_of_is_contr 0 m), apply subtype_eq,
  exact (to_respect_zero φ)^-1
Defined.

Definition image_module_isomorphism (φ : M₁ ->lm M₂)
  (H : is_surjective φ) : image_module φ <~>lm M₂.
submodule_isomorphism _ H

Definition has_scalar_kernel (φ : M₁ ->lm M₂) (m : M₁) (r : R)
  (p : φ m = 0) : φ (r • m) = 0.
Proof.
  refine to_respect_smul φ r m @ ap (fun x => r • x) p @ smul_zero r,
Defined.

Definition lm_kernel (φ : M₁ ->lm M₂) : property M₁ . kernel (group_homomorphism_of_lm_homomorphism φ)

Definition is_submodule_kernel [instance] (φ : M₁ ->lm M₂) : is_submodule M₁ (lm_kernel φ).
is_submodule.mk
  (show 0 ∈ kernel (group_homomorphism_of_lm_homomorphism φ),
Proof. apply is_subgroup.one_mem, apply is_subgroup_kernel end)
  (fun g₁ g₂ hg₁ hg₂ =>
  show g₁ + g₂ ∈ kernel (group_homomorphism_of_lm_homomorphism φ),
Proof. apply @is_subgroup.mul_mem, apply is_subgroup_kernel, exact hg₁, exact hg₂ end)
  (has_scalar_kernel φ)

Definition kernel_full (φ : M₁ ->lm M₂) (H : is_contr M₂) (m : M₁) : m ∈ lm_kernel φ.
!is_prop.elim

Definition kernel_module (φ : M₁ ->lm M₂) : LeftModule R . submodule (lm_kernel φ)

Definition is_contr_kernel_module [instance] (φ : M₁ ->lm M₂) (H : is_contr M₁) :
  is_contr (kernel_module φ).
is_contr_submodule _ _

Definition kernel_module_isomorphism (φ : M₁ ->lm M₂) (H : is_contr M₂) :
  kernel_module φ <~>lm M₁.
submodule_isomorphism _ (kernel_full φ _)

Definition homology_quotient_property (ψ : M₂ ->lm M₃) (φ : M₁ ->lm M₂) :
  property (kernel_module ψ).
property_submodule (lm_kernel ψ) (image (homomorphism_fn φ))

Definition is_submodule_homology_property [instance] (ψ : M₂ ->lm M₃) (φ : M₁ ->lm M₂) :
  is_submodule (kernel_module ψ) (homology_quotient_property ψ φ).
(is_submodule_property_submodule _ (image φ))

Definition homology (ψ : M₂ ->lm M₃) (φ : M₁ ->lm M₂) : LeftModule R.
quotient_module (homology_quotient_property ψ φ)

Definition homology.mk (φ : M₁ ->lm M₂) (m : M₂) (h : ψ m = 0) : homology ψ φ.
quotient_map (homology_quotient_property ψ φ) ⟨m, h⟩

Definition homology_eq0 {m : M₂} {hm : ψ m = 0} (h : image φ m) :
  homology.mk φ m hm = 0.
ab_qg_map_eq_one _ h

Definition homology_eq0' {m : M₂} {hm : ψ m = 0} (h : image φ m):
  homology.mk φ m hm = homology.mk φ 0 (to_respect_zero ψ).
ab_qg_map_eq_one _ h

Definition homology_eq {m n : M₂} {hm : ψ m = 0} {hn : ψ n = 0} (h : image φ (m - n)) :
  homology.mk φ m hm = homology.mk φ n hn.
eq_of_sub_eq_zero (homology_eq0 h)

Definition homology_elim (θ : M₂ ->lm M) (H : forall m, θ (φ m) = 0) :
  homology ψ φ ->lm M.
quotient_elim (θ olm submodule_incl _)
Proof.
  intro m x,
  induction m with m h,
  esimp at *,
  induction x with v,
  exact ap θ p^-1 @ H v   end

Definition is_contr_homology [instance] (ψ : M₂ ->lm M₃) (φ : M₁ ->lm M₂) (H : is_contr M₂) :
  is_contr (homology ψ φ).
is_contr_quotient_module _ (is_contr_kernel_module _ _)

Definition homology_isomorphism (ψ : M₂ ->lm M₃) (φ : M₁ ->lm M₂)
  (H₁ : is_contr M₁) (H₃ : is_contr M₃) : homology ψ φ <~>lm M₂.
(quotient_module_isomorphism (homology_quotient_property ψ φ)
  (eq_zero_of_mem_property_submodule_trivial (image_trivial _))) @lm (kernel_module_isomorphism ψ _)

Definition homology_functor (α₁ : M₁ ->lm M₁') (α₂ : M₂ ->lm M₂') (α₃ : M₃ ->lm M₃')
  (p : hsquare ψ ψ' α₂ α₃) (q : hsquare φ φ' α₁ α₂) : homology ψ φ ->lm homology ψ' φ'.
Proof.
  fapply quotient_module_functor =>
  { apply submodule_functor α₂ => intro m pm, refine (p m)^-1 @ ap α₃ pm @ to_respect_zero α₃ },
  { intro m pm, induction pm with m' pm',
  refine image.mk (α₁ m') ((q m')^-1 @ _), exact ap α₂ pm' }
Defined.

Definition homology_isomorphism_homology (α₁ : M₁ <~>lm M₁') (α₂ : M₂ <~>lm M₂') (α₃ : M₃ <~>lm M₃')
  (p : hsquare ψ ψ' α₂ α₃) (q : hsquare φ φ' α₁ α₂) : homology ψ φ <~>lm homology ψ' φ'.
Proof.
  fapply quotient_module_isomorphism_quotient_module,
  { fapply submodule_isomorphism_submodule α₂, intro m,
  exact iff.intro (fun pm => (p m)^-1 @ ap α₃ pm @ to_respect_zero α₃)
  (fun pm => inj (equiv_of_isomorphism α₃) (p m @ pm @ (to_respect_zero α₃)^-1)) },
  { intro m, apply iff.intro,
  { intro pm, induction pm with m' pm', refine image.mk (α₁ m') ((q m')^-1 @ _), exact ap α₂ pm' },
  { intro pm, induction pm with m' pm', refine image.mk (α₁^-1ˡᵐ m') _,
  refine (hvinverse' (equiv_of_isomorphism α₁) (equiv_of_isomorphism α₂) q m')^-1 @ _,
  exact ap α₂^-1ˡᵐ pm' @ to_left_inv (equiv_of_isomorphism α₂) m.1 }}
Defined.

Definition ker_in_im_of_is_contr_homology (ψ : M₂ ->lm M₃) {φ : M₁ ->lm M₂}
  (H₁ : is_contr (homology ψ φ)) {m : M₂} (p : ψ m = 0) : image φ m.
rel_of_is_contr_quotient_module _ H₁ ⟨m, p⟩

Definition is_embedding_of_is_contr_homology_of_constant {ψ : M₂ ->lm M₃} (φ : M₁ ->lm M₂)
  (H₁ : is_contr (homology ψ φ)) (H₂ : forall m, φ m = 0) : is_embedding ψ.
Proof.
  apply to_is_embedding_homomorphism (group_homomorphism_of_lm_homomorphism ψ),
  intro m p, note H . rel_of_is_contr_quotient_module _ H₁ ⟨m, p⟩,
  induction H with n q,
  exact q^-1 @ H₂ n
Defined.

Definition is_embedding_of_is_contr_homology_of_is_contr {ψ : M₂ ->lm M₃} (φ : M₁ ->lm M₂)
  (H₁ : is_contr (homology ψ φ)) (H₂ : is_contr M₁) : is_embedding ψ.
is_embedding_of_is_contr_homology_of_constant φ H₁
  (fun m => ap φ (@eq_of_is_contr _ H₂ _ _) @ respect_zero φ)

Definition is_surjective_of_is_contr_homology_of_constant (ψ : M₂ ->lm M₃) {φ : M₁ ->lm M₂}
  (H₁ : is_contr (homology ψ φ)) (H₂ : forall m, ψ m = 0) : is_surjective φ.
fun m => ker_in_im_of_is_contr_homology ψ H₁ (H₂ m)

Definition is_surjective_of_is_contr_homology_of_is_contr (ψ : M₂ ->lm M₃) {φ : M₁ ->lm M₂}
  (H₁ : is_contr (homology ψ φ)) (H₂ : is_contr M₃) : is_surjective φ.
is_surjective_of_is_contr_homology_of_constant ψ H₁ (fun m => @eq_of_is_contr _ H₂ _ _)

Definition homology_isomorphism_kernel_module (ψ : M₂ ->lm M₃) (φ : M₁ ->lm M₂)
  (H : forall m, image φ m -> m = 0) : homology ψ φ <~>lm kernel_module ψ.
Proof.
  apply quotient_module_isomorphism, intro m h, apply subtype_eq, apply H, exact h
Defined.

Definition cokernel_module (φ : M₁ ->lm M₂) : LeftModule R.
quotient_module (image φ)

Definition homology_isomorphism_cokernel_module (ψ : M₂ ->lm M₃) (φ : M₁ ->lm M₂) (H : forall m, ψ m = 0) :
  homology ψ φ <~>lm cokernel_module φ.
quotient_module_isomorphism_quotient_module
  (submodule_isomorphism _ H)
Proof. intro m, reflexivity end

open chain_complex fin nat
Definition LES_of_SESs {N : succ_str} (A B C : N -> LeftModule.{_ u} R) (φ : forall n, A n ->lm B n)
  (ses : forall n : N, short_exact_mod (cokernel_module (φ (succ_str.S n))) (C n) (kernel_module (φ n))) :
  module_chain_complex.{_ _ u} R (stratified N 2).
Proof.
  fapply module_chain_complex.mk,
  { intro x, induction x with n k, induction k with k H, do 3 (cases k with k; rotate 1),
  { (*k≥3*) exfalso, apply lt_le_antisymm H, apply le_add_left},
  { (*k=0*) exact B n },
  { (*k=1*) exact A n },
  { (*k=2*) exact C n }},
  { intro x, induction x with n k, induction k with k H, do 3 (cases k with k; rotate 1),
  { (*k≥3*) exfalso, apply lt_le_antisymm H, apply le_add_left},
  { (*k=0*) exact φ n },
  { (*k=1*) exact submodule_incl _ olm short_exact_mod.g (ses n) },
  { (*k=2*) change B (succ_str.S n) ->lm C n, exact short_exact_mod.f (ses n) olm !quotient_map }},
  { intros x m, induction x with n k, induction k with k H, do 3 (cases k with k; rotate 1),
  { exfalso, apply lt_le_antisymm H, apply le_add_left},
  { exact (short_exact_mod.g (ses n) m).2 },
  { note h . is_short_exact.im_in_ker (short_exact_mod.h (ses n)) (quotient_map _ m),
  exact ap pr1 h },
  { refine _ @ to_respect_zero (short_exact_mod.f (ses n)),
  rexact ap (short_exact_mod.f (ses n)) (quotient_map_eq_zero _ _ (image.mk m idp)) }}
Defined.

open prod
Definition LES_of_SESs_zero {N : succ_str} {A B C : N -> LeftModule.{_ u} R} (φ : forall n, A n ->lm B n)
  (ses : forall n : N, short_exact_mod (cokernel_module (φ (succ_str.S n))) (C n) (kernel_module (φ n)))
  (n : N) : LES_of_SESs A B C φ ses (n, 0) <~>lm B n.
by reflexivity

Definition LES_of_SESs_one {N : succ_str} {A B C : N -> LeftModule.{_ u} R} (φ : forall n, A n ->lm B n)
  (ses : forall n : N, short_exact_mod (cokernel_module (φ (succ_str.S n))) (C n) (kernel_module (φ n)))
  (n : N) : LES_of_SESs A B C φ ses (n, 1) <~>lm A n.
by reflexivity

Definition LES_of_SESs_two {N : succ_str} {A B C : N -> LeftModule.{_ u} R} (φ : forall n, A n ->lm B n)
  (ses : forall n : N, short_exact_mod (cokernel_module (φ (succ_str.S n))) (C n) (kernel_module (φ n)))
  (n : N) : LES_of_SESs A B C φ ses (n, 2) <~>lm C n.
by reflexivity

Definition is_exact_LES_of_SESs {N : succ_str} {A B C : N -> LeftModule.{_ u} R}
  (φ : forall n, A n ->lm B n)
  (ses : forall n : N, short_exact_mod (cokernel_module (φ (succ_str.S n))) (C n) (kernel_module (φ n))) :
  is_exact_m (LES_of_SESs A B C φ ses).
Proof.
  intros x m p, induction x with n k, induction k with k H, do 3 (cases k with k; rotate 1),
  { exfalso, apply lt_le_antisymm H, apply le_add_left},
  { induction is_short_exact.is_surj (short_exact_mod.h (ses n)) ⟨m, p⟩ with m' q,
  exact image.mk m' (ap pr1 q) },
  { induction is_short_exact.ker_in_im (short_exact_mod.h (ses n)) m (subtype_eq p) with m' q,
  induction m' using set_quotient.rec_prop with m',
  exact image.mk m' q },
  { apply rel_of_quotient_map_eq_zero (image (φ (succ_str.S n))) m,
  apply @is_injective_of_is_embedding _ _ _ (is_short_exact.is_emb (short_exact_mod.h (ses n))),
  exact p @ (to_respect_zero (short_exact_mod.f (ses n)))^-1 }
Defined.






Defined. left_module
