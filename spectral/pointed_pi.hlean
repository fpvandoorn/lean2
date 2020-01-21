(*
Copyright (c) 2016 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Floris van Doorn
-/

import homotopy.connectedness types.pointed2 .move_to_lib .pointed

open eq pointed equiv sigma is_equiv trunc option pi function fiber

(*
  In this file we define dependent pointed maps and properties of them.

  Using this, we give the truncation level
  of the type of pointed maps, giving the connectivity of
  the domain and the truncation level of the codomain.
  This is is_trunc_pmap_of_is_conn at the end.

  We also prove other properties about pointed (dependent maps), like the fact that
  (Π*a, F a) → (Π*a, X a) → (Π*a, B a)
  is a fibration sequence if (F a) → (X a) → B a) is.
-/

namespace pointed

  (* the pointed type of unpointed (nondependent) maps -/
  definition pumap [constructor] (A : Type) (B : Type*) : Type* :=
  pointed.MK (A → B) (const A pt)

  (* the pointed type of unpointed dependent maps -/
  definition pupi [constructor] {A : Type} (B : A → Type*) : Type* :=
  pointed.MK (Πa, B a) (λa, pt)

  notation `Πᵘ*` binders `, ` r:(scoped P, pupi P) := r
  infix ` →ᵘ* `:30 := pumap

  (* stuff about the pointed type of unpointed maps (dependent and non-dependent) -/
  definition sigma_pumap {A : Type} (B : A → Type) (C : Type*) :
    ((Σa, B a) →ᵘ* C) ≃* Πᵘ*a, B a →ᵘ* C :=
  pequiv_of_equiv (equiv_sigma_rec _)⁻¹ᵉ idp

  definition phomotopy_mk_pupi [constructor] {A : Type*} {B : Type} {C : B → Type*}
    {f g : A →* (Πᵘ*b, C b)} (p : f ~2 g)
    (q : p pt ⬝hty apd10 (respect_pt g) ~ apd10 (respect_pt f)) : f ~* g :=
  begin
    apply phomotopy.mk (λa, eq_of_homotopy (p a)),
    apply inj !eq_equiv_homotopy,
    apply eq_of_homotopy, intro b,
    refine !apd10_con ⬝ _,
    refine whisker_right _ !apd10_eq_of_homotopy ⬝ q b
  end

  definition pupi_functor [constructor] {A A' : Type} {B : A → Type*} {B' : A' → Type*}
    (f : A' → A) (g : Πa, B (f a) →* B' a) : (Πᵘ*a, B a) →* (Πᵘ*a', B' a') :=
  pmap.mk (pi_functor f g) (eq_of_homotopy (λa, respect_pt (g a)))

  definition pupi_functor_right [constructor] {A : Type} {B B' : A → Type*}
    (g : Πa, B a →* B' a) : (Πᵘ*a, B a) →* (Πᵘ*a, B' a) :=
  pupi_functor id g

  definition pupi_functor_compose {A A' A'' : Type}
    {B : A → Type*} {B' : A' → Type*} {B'' : A'' → Type*} (f : A'' → A') (f' : A' → A)
    (g' : Πa, B' (f a) →* B'' a) (g : Πa, B (f' a) →* B' a) :
    pupi_functor (f' ∘ f) (λa, g' a ∘* g (f a)) ~* pupi_functor f g' ∘* pupi_functor f' g :=
  begin
    fapply phomotopy_mk_pupi,
    { intro h a, reflexivity },
    { intro a, refine !idp_con ⬝ _, refine !apd10_con ⬝ _ ⬝ !apd10_eq_of_homotopy⁻¹, esimp,
      refine (!apd10_prepostcompose ⬝ ap02 (g' a) !apd10_eq_of_homotopy) ◾
             !apd10_eq_of_homotopy }
  end

  definition pupi_functor_pid (A : Type) (B : A → Type*) :
    pupi_functor id (λa, pid (B a)) ~* pid (Πᵘ*a, B a) :=
  begin
    fapply phomotopy_mk_pupi,
    { intro h a, reflexivity },
    { intro a, refine !idp_con ⬝ !apd10_eq_of_homotopy⁻¹ }
  end

  definition pupi_functor_phomotopy {A A' : Type} {B : A → Type*} {B' : A' → Type*}
    {f f' : A' → A} {g : Πa, B (f a) →* B' a} {g' : Πa, B (f' a) →* B' a}
    (p : f ~ f') (q : Πa, g a ~* g' a ∘* ptransport B (p a)) :
    pupi_functor f g ~* pupi_functor f' g' :=
  begin
    fapply phomotopy_mk_pupi,
    { intro h a, exact q a (h (f a)) ⬝ ap (g' a) (apdt h (p a)) },
    { intro a, esimp,
     exact whisker_left _ !apd10_eq_of_homotopy ⬝ !con.assoc ⬝
           to_homotopy_pt (q a) ⬝ !apd10_eq_of_homotopy⁻¹ }
  end

  definition pupi_pequiv [constructor] {A A' : Type} {B : A → Type*} {B' : A' → Type*}
    (e : A' ≃ A) (f : Πa, B (e a) ≃* B' a) :
    (Πᵘ*a, B a) ≃* (Πᵘ*a', B' a') :=
  pequiv.MK (pupi_functor e f)
            (pupi_functor e⁻¹ᵉ (λa, ptransport B (right_inv e a) ∘* (f (e⁻¹ᵉ a))⁻¹ᵉ*))
    abstract begin
      refine !pupi_functor_compose⁻¹* ⬝* pupi_functor_phomotopy (to_right_inv e) _ ⬝*
             !pupi_functor_pid,
      intro a, exact !pinv_pcompose_cancel_right ⬝* !pid_pcompose⁻¹*
    end end
    abstract begin
      refine !pupi_functor_compose⁻¹* ⬝* pupi_functor_phomotopy (to_left_inv e) _ ⬝*
             !pupi_functor_pid,
      intro a, refine !passoc⁻¹* ⬝* pinv_right_phomotopy_of_phomotopy _ ⬝* !pid_pcompose⁻¹*,
      refine pwhisker_left _ _ ⬝* !ptransport_natural,
      exact ptransport_change_eq _ (adj e a) ⬝* ptransport_ap B e (to_left_inv e a)
    end end

  definition pupi_pequiv_right [constructor] {A : Type} {B B' : A → Type*} (f : Πa, B a ≃* B' a) :
    (Πᵘ*a, B a) ≃* (Πᵘ*a, B' a) :=
  pupi_pequiv erfl f

  definition loop_pupi [constructor] {A : Type} (B : A → Type*) : Ω (Πᵘ*a, B a) ≃* Πᵘ*a, Ω (B a) :=
  pequiv_of_equiv !eq_equiv_homotopy idp

  -- definition loop_pupi_natural [constructor] {A : Type} {B B' : A → Type*} (f : Πa, B a →* B' a) :
  --   psquare (Ω→ (pupi_functor_right f)) (pupi_functor_right (λa, Ω→ (f a)))
  --           (loop_pupi B) (loop_pupi B') :=

  definition ap1_gen_pi {A A' : Type} {B : A → Type} {B' : A' → Type}
    {h₀ h₁ : Πa, B a} {h₀' h₁' : Πa', B' a'} (f : A' → A) (g : Πa, B (f a) → B' a)
    (p₀ : pi_functor f g h₀ ~ h₀') (p₁ : pi_functor f g h₁ ~ h₁') (r : h₀ = h₁) (a' : A') :
    apd10 (ap1_gen (pi_functor f g) (eq_of_homotopy p₀) (eq_of_homotopy p₁) r) a' =
    ap1_gen (g a') (p₀ a') (p₁ a') (apd10 r (f a')) :=
  begin
    induction r, induction p₀ using homotopy.rec_idp, induction p₁ using homotopy.rec_idp, esimp,
    exact apd10 (ap apd10 !ap1_gen_idp) a',


--    exact ap (λx, apd10 (ap1_gen _ x x _) _) !eq_of_homotopy_idp
  end

  definition ap1_gen_pi_idp {A A' : Type} {B : A → Type} {B' : A' → Type}
    {h₀ : Πa, B a} (f : A' → A) (g : Πa, B (f a) → B' a) (a' : A') :
    ap1_gen_pi f g (homotopy.refl (pi_functor f g h₀)) (homotopy.refl (pi_functor f g h₀)) idp a' =
    apd10 (ap apd10 !ap1_gen_idp) a' :=
--    apd10 (ap apd10 (ap1_gen_idp (pi_functor id f) (eq_of_homotopy (λ a, idp)))) a' :=
    -- ap (λp, apd10 p a') (ap1_gen_idp (pi_functor f g) (eq_of_homotopy homotopy.rfl)) :=
  begin
    esimp [ap1_gen_pi],
    refine !homotopy_rec_idp_refl ⬝ !homotopy_rec_idp_refl,
  end
-- print homotopy.rec_
-- print apd10_ap_postcompose
-- print pi_functor
-- print ap1_gen_idp
-- print ap1_gen_pi

  definition loop_pupi_natural [constructor] {A : Type} {B B' : A → Type*} (f : Πa, B a →* B' a) :
    psquare (Ω→ (pupi_functor_right f)) (pupi_functor_right (λa, Ω→ (f a)))
            (loop_pupi B) (loop_pupi B') :=
  begin
    fapply phomotopy_mk_pupi,
    { intro p a, exact ap1_gen_pi id f (λa, respect_pt (f a)) (λa, respect_pt (f a)) p a },
    { intro a, revert B' f, refine fiberwise_pointed_map_rec _ _, intro B' f,
      refine !ap1_gen_pi_idp ◾ (ap (λx, apd10 x _) !idp_con ⬝ !apd10_eq_of_homotopy) }
  end

  definition phomotopy_mk_pumap [constructor] {A C : Type*} {B : Type} {f g : A →* (B →ᵘ* C)}
    (p : f ~2 g) (q : p pt ⬝hty apd10 (respect_pt g) ~ apd10 (respect_pt f))
    : f ~* g :=
  phomotopy_mk_pupi p q

  definition pumap_functor [constructor] {A A' : Type} {B B' : Type*} (f : A' → A) (g : B →* B') :
    (A →ᵘ* B) →* (A' →ᵘ* B') :=
  pupi_functor f (λa, g)

  definition pumap_functor_compose {A A' A'' : Type} {B B' B'' : Type*}
    (f : A'' → A') (f' : A' → A) (g' : B' →* B'') (g : B →* B') :
    pumap_functor (f' ∘ f) (g' ∘* g) ~* pumap_functor f g' ∘* pumap_functor f' g :=
  pupi_functor_compose f f' (λa, g') (λa, g)

  definition pumap_functor_pid (A : Type) (B : Type*) :
    pumap_functor id (pid B) ~* pid (A →ᵘ* B) :=
  pupi_functor_pid A (λa, B)

  definition pumap_functor_phomotopy {A A' : Type} {B B' : Type*} {f f' : A' → A} {g g' : B →* B'}
    (p : f ~ f') (q : g ~* g') : pumap_functor f g ~* pumap_functor f' g' :=
  pupi_functor_phomotopy p (λa, q ⬝* !pcompose_pid⁻¹* ⬝* pwhisker_left _ !ptransport_constant⁻¹*)

  definition pumap_pequiv [constructor] {A A' : Type} {B B' : Type*} (e : A ≃ A') (f : B ≃* B') :
    (A →ᵘ* B) ≃* (A' →ᵘ* B') :=
  pupi_pequiv e⁻¹ᵉ (λa, f)

  definition pumap_pequiv_right [constructor] (A : Type) {B B' : Type*} (f : B ≃* B') :
    (A →ᵘ* B) ≃* (A →ᵘ* B') :=
  pumap_pequiv erfl f

  definition pumap_pequiv_left [constructor] {A A' : Type} (B : Type*) (f : A ≃ A') :
    (A →ᵘ* B) ≃* (A' →ᵘ* B) :=
  pumap_pequiv f pequiv.rfl

  definition loop_pumap [constructor] (A : Type) (B : Type*) : Ω (A →ᵘ* B) ≃* A →ᵘ* Ω B :=
  loop_pupi (λa, B)

  (* the pointed sigma type -/
  definition psigma_gen [constructor] {A : Type*} (P : A → Type) (x : P pt) : Type* :=
  pointed.MK (Σa, P a) ⟨pt, x⟩

  definition psigma_gen_functor [constructor] {A A' : Type*} {B : A → Type}
    {B' : A' → Type} {b : B pt} {b' : B' pt} (f : A →* A')
    (g : Πa, B a → B' (f a)) (p : g pt b =[respect_pt f] b') : psigma_gen B b →* psigma_gen B' b' :=
  pmap.mk (sigma_functor f g) (sigma_eq (respect_pt f) p)

  definition psigma_gen_functor_right [constructor] {A : Type*} {B B' : A → Type}
    {b : B pt} {b' : B' pt} (f : Πa, B a → B' a) (p : f pt b = b') :
    psigma_gen B b →* psigma_gen B' b' :=
  proof pmap.mk (sigma_functor id f) (sigma_eq_right p) qed

  definition psigma_gen_pequiv_psigma_gen [constructor] {A A' : Type*} {B : A → Type}
    {B' : A' → Type} {b : B pt} {b' : B' pt} (f : A ≃* A')
    (g : Πa, B a ≃ B' (f a)) (p : g pt b =[respect_pt f] b') : psigma_gen B b ≃* psigma_gen B' b' :=
  pequiv_of_equiv (sigma_equiv_sigma f g) (sigma_eq (respect_pt f) p)

  definition psigma_gen_pequiv_psigma_gen_left [constructor] {A A' : Type*} {B : A' → Type}
    {b : B pt} (f : A ≃* A') {b' : B (f pt)} (q : b' =[respect_pt f] b) :
    psigma_gen (B ∘ f) b' ≃* psigma_gen B b :=
  psigma_gen_pequiv_psigma_gen f (λa, erfl) q

  definition psigma_gen_pequiv_psigma_gen_right [constructor] {A : Type*} {B B' : A → Type}
    {b : B pt} {b' : B' pt} (f : Πa, B a ≃ B' a) (p : f pt b = b') :
    psigma_gen B b ≃* psigma_gen B' b' :=
  psigma_gen_pequiv_psigma_gen pequiv.rfl f (pathover_idp_of_eq p)

  definition psigma_gen_pequiv_psigma_gen_basepoint [constructor] {A : Type*} {B : A → Type}
    {b b' : B pt} (p : b = b') : psigma_gen B b ≃* psigma_gen B b' :=
  psigma_gen_pequiv_psigma_gen_right (λa, erfl) p

  definition loop_psigma_gen [constructor] {A : Type*} (B : A → Type) (b₀ : B pt) :
    Ω (psigma_gen B b₀) ≃* @psigma_gen (Ω A) (λp, pathover B b₀ p b₀) idpo :=
  pequiv_of_equiv (sigma_eq_equiv pt pt) idp

  open sigma.ops
  definition ap1_gen_sigma {A A' : Type} {B : A → Type} {B' : A' → Type}
    {x₀ x₁ : Σa, B a} {a₀' a₁' : A'} {b₀' : B' a₀'} {b₁' : B' a₁'} (f : A → A')
    (p₀ : f x₀.1 = a₀') (p₁ : f x₁.1 = a₁') (g : Πa, B a → B' (f a))
    (q₀ : g x₀.1 x₀.2 =[p₀] b₀') (q₁ : g x₁.1 x₁.2 =[p₁] b₁') (r : x₀ = x₁) :
    (λx, ⟨x..1, x..2⟩) (ap1_gen (sigma_functor f g) (sigma_eq p₀ q₀) (sigma_eq p₁ q₁) r) =
    ⟨ap1_gen f p₀ p₁ r..1, q₀⁻¹ᵒ ⬝o pathover_ap B' f (apo g r..2) ⬝o q₁⟩ :=
  begin
    induction r, induction q₀, induction q₁, reflexivity
  end

  definition loop_psigma_gen_natural {A A' : Type*} {B : A → Type}
    {B' : A' → Type} {b : B pt} {b' : B' pt} (f : A →* A')
    (g : Πa, B a → B' (f a)) (p : g pt b =[respect_pt f] b') :
    psquare (Ω→ (psigma_gen_functor f g p))
            (psigma_gen_functor (Ω→ f) (λq r, p⁻¹ᵒ ⬝o pathover_ap _ _ (apo g r) ⬝o p)
            !cono.left_inv)
            (loop_psigma_gen B b) (loop_psigma_gen B' b') :=
  begin
    fapply phomotopy.mk,
    { exact ap1_gen_sigma f (respect_pt f) (respect_pt f) g p p },
    { induction f with f f₀, induction A' with A' a₀', esimp at * ⊢, induction p, reflexivity }
  end

  definition psigma_gen_functor_pcompose [constructor] {A₁ A₂ A₃ : Type*}
    {B₁ : A₁ → Type} {B₂ : A₂ → Type} {B₃ : A₃ → Type}
    {b₁ : B₁ pt} {b₂ : B₂ pt} {b₃ : B₃ pt}
    {f₁ : A₁ →* A₂} {f₂ : A₂ →* A₃}
    (g₁ : Π⦃a⦄, B₁ a → B₂ (f₁ a)) (g₂ : Π⦃a⦄, B₂ a → B₃ (f₂ a))
    (p₁ : pathover B₂ (g₁ b₁) (respect_pt f₁) b₂)
    (p₂ : pathover B₃ (g₂ b₂) (respect_pt f₂) b₃) :
    psigma_gen_functor (f₂ ∘* f₁) (λa, @g₂ (f₁ a) ∘ @g₁ a) (pathover_ap B₃ f₂ (apo g₂ p₁) ⬝o p₂) ~*
    psigma_gen_functor f₂ g₂ p₂ ∘* psigma_gen_functor f₁ g₁ p₁ :=
  begin
    fapply phomotopy.mk,
    { intro x, reflexivity },
    { refine !idp_con ⬝ _, esimp,
      refine whisker_right _ !ap_sigma_functor_sigma_eq ⬝ _,
      induction f₁ with f₁ f₁₀, induction f₂ with f₂ f₂₀, induction A₂ with A₂ a₂₀,
      induction A₃ with A₃ a₃₀, esimp at * ⊢, induction p₁, induction p₂, reflexivity }
  end

  definition psigma_gen_functor_phomotopy [constructor] {A₁ A₂ : Type*}
    {B₁ : A₁ → Type} {B₂ : A₂ → Type} {b₁ : B₁ pt} {b₂ : B₂ pt} {f₁ f₂ : A₁ →* A₂}
    {g₁ : Π⦃a⦄, B₁ a → B₂ (f₁ a)} {g₂ : Π⦃a⦄, B₁ a → B₂ (f₂ a)}
    {p₁ : pathover B₂ (g₁ b₁) (respect_pt f₁) b₂} {p₂ : pathover B₂ (g₂ b₁) (respect_pt f₂) b₂}
    (h₁ : f₁ ~* f₂)
    (h₂ : Π⦃a⦄ (b : B₁ a), pathover B₂ (g₁ b) (h₁ a) (g₂ b))
    (h₃ : squareover B₂ (square_of_eq (to_homotopy_pt h₁)⁻¹) p₁ p₂ (h₂ b₁) idpo) :
    psigma_gen_functor f₁ g₁ p₁ ~* psigma_gen_functor f₂ g₂ p₂ :=
  begin
    induction h₁ using phomotopy_rec_idp,
    fapply phomotopy.mk,
    { intro x, induction x with a b, exact ap (dpair (f₁ a)) (eq_of_pathover_idp (h₂ b)) },
    { induction f₁ with f f₀, induction A₂ with A₂ a₂₀, esimp at * ⊢,
      induction f₀, esimp, induction p₂ using idp_rec_on,
      rewrite [to_right_inv !eq_con_inv_equiv_con_eq at h₃],
      have h₂ b₁ = p₁, from (eq_top_of_squareover h₃)⁻¹, induction this,
      refine !ap_dpair ⬝ ap (sigma_eq _) _, exact to_left_inv !pathover_idp (h₂ b₁) }
  end

  definition psigma_gen_functor_psquare [constructor] {A₀₀ A₀₂ A₂₀ A₂₂ : Type*}
    {B₀₀ : A₀₀ → Type} {B₀₂ : A₀₂ → Type} {B₂₀ : A₂₀ → Type} {B₂₂ : A₂₂ → Type}
    {b₀₀ : B₀₀ pt} {b₀₂ : B₀₂ pt} {b₂₀ : B₂₀ pt} {b₂₂ : B₂₂ pt}
    {f₀₁ : A₀₀ →* A₀₂} {f₁₀ : A₀₀ →* A₂₀} {f₂₁ : A₂₀ →* A₂₂} {f₁₂ : A₀₂ →* A₂₂}
    {g₀₁ : Π⦃a⦄, B₀₀ a → B₀₂ (f₀₁ a)} {g₁₀ : Π⦃a⦄, B₀₀ a → B₂₀ (f₁₀ a)}
    {g₂₁ : Π⦃a⦄, B₂₀ a → B₂₂ (f₂₁ a)} {g₁₂ : Π⦃a⦄, B₀₂ a → B₂₂ (f₁₂ a)}
    {p₀₁ : pathover B₀₂ (g₀₁ b₀₀) (respect_pt f₀₁) b₀₂}
    {p₁₀ : pathover B₂₀ (g₁₀ b₀₀) (respect_pt f₁₀) b₂₀}
    {p₂₁ : pathover B₂₂ (g₂₁ b₂₀) (respect_pt f₂₁) b₂₂}
    {p₁₂ : pathover B₂₂ (g₁₂ b₀₂) (respect_pt f₁₂) b₂₂}
    (h₁ : psquare f₁₀ f₁₂ f₀₁ f₂₁)
    (h₂ : Π⦃a⦄ (b : B₀₀ a), pathover B₂₂ (g₂₁ (g₁₀ b)) (h₁ a) (g₁₂ (g₀₁ b)))
    (h₃ : squareover B₂₂ (square_of_eq (to_homotopy_pt h₁)⁻¹)
                         (pathover_ap B₂₂ f₂₁ (apo g₂₁ p₁₀) ⬝o p₂₁)
                         (pathover_ap B₂₂ f₁₂ (apo g₁₂ p₀₁) ⬝o p₁₂)
                         (h₂ b₀₀) idpo) :
    psquare (psigma_gen_functor f₁₀ g₁₀ p₁₀) (psigma_gen_functor f₁₂ g₁₂ p₁₂)
            (psigma_gen_functor f₀₁ g₀₁ p₀₁) (psigma_gen_functor f₂₁ g₂₁ p₂₁) :=
  proof
    !psigma_gen_functor_pcompose⁻¹* ⬝*
    psigma_gen_functor_phomotopy h₁ h₂ h₃ ⬝*
    !psigma_gen_functor_pcompose
  qed


end pointed open pointed

namespace pointed

  definition pointed_respect_pt [instance] [constructor] {A B : Type*} (f : A →* B) :
    pointed (f pt = pt) :=
  pointed.mk (respect_pt f)

  definition ppi_of_phomotopy [constructor] {A B : Type*} {f g : A →* B} (h : f ~* g) :
    ppi (λx, f x = g x) (respect_pt f ⬝ (respect_pt g)⁻¹) :=
  h

  definition phomotopy {A : Type*} {P : A → Type} {x : P pt} (f g : ppi P x) : Type :=
  ppi (λa, f a = g a) (respect_pt f ⬝ (respect_pt g)⁻¹)

  variables {A A' A'' : Type*} {P Q R : A → Type*} {P' : A' → Type*} {f g h : Π*a, P a}
            {B C D : A → Type} {b₀ : B pt} {c₀ : C pt} {d₀ : D pt}
            {k k' l m : ppi B b₀}

  definition pppi_equiv_pmap [constructor] (A B : Type*) : (Π*(a : A), B) ≃ (A →* B) :=
  by reflexivity

  definition pppi_pequiv_ppmap [constructor] (A B : Type*) : (Π*(a : A), B) ≃* ppmap A B :=
  by reflexivity

  definition apd10_to_fun_eq_of_phomotopy (h : f ~* g)
    : apd10 (ap (λ k, pppi.to_fun k) (eq_of_phomotopy h)) = h :=
  begin
    induction h using phomotopy_rec_idp,
    xrewrite [eq_of_phomotopy_refl f]
  end

--  definition phomotopy_of_eq_of_phomotopy

  definition phomotopy_mk_ppi [constructor] {A : Type*} {B : Type*} {C : B → Type*}
    {f g : A →* (Π*b, C b)} (p : Πa, f a ~* g a)
    (q : p pt ⬝* phomotopy_of_eq (respect_pt g) = phomotopy_of_eq (respect_pt f)) : f ~* g :=
  begin
    apply phomotopy.mk (λa, eq_of_phomotopy (p a)),
    apply inj !ppi_eq_equiv,
    refine !phomotopy_of_eq_con ⬝ _, esimp,
    refine ap (λx, x ⬝* _) !phomotopy_of_eq_of_phomotopy ⬝ q
  end

--   definition phomotopy_mk_ppmap [constructor]
--     {A : Type*} {X : A → Type*} {Y : Π (a : A), X a → Type*}
--     {f g : Π* (a : A), Π*(x : (X a)), (Y a x)}
--     (p : Πa, f a ~* g a)
--     (q : p pt ⬝* phomotopy_of_eq (ppi_resp_pt g) = phomotopy_of_eq (ppi_resp_pt f))
--     : f ~* g :=
--   begin
--     apply phomotopy.mk (λa, eq_of_phomotopy (p a)),
--     apply inj (ppi_eq_equiv _ _),
--     refine !phomotopy_of_eq_con ⬝ _,
-- --    refine !phomotopy_of_eq_of_phomotopy ◾** idp ⬝ q,
--   end

  variable {k}

  variables (k l)

  definition ppi_loop_equiv : (k = k) ≃ Π*(a : A), Ω (pType.mk (B a) (k a)) :=
  begin
    induction k with k p, induction p,
    exact ppi_eq_equiv (ppi.mk k idp) (ppi.mk k idp)
  end

  variables {k l}
  -- definition eq_of_phomotopy (h : k ~* l) : k = l :=
  -- (ppi_eq_equiv k l)⁻¹ᵉ h

  definition ppi_functor_right [constructor] {A : Type*} {B B' : A → Type}
    {b : B pt} {b' : B' pt} (f : Πa, B a → B' a) (p : f pt b = b') (g : ppi B b)
    : ppi B' b' :=
  ppi.mk (λa, f a (g a)) (ap (f pt) (respect_pt g) ⬝ p)

  definition ppi_functor_right_compose [constructor] {A : Type*} {B₁ B₂ B₃ : A → Type}
    {b₁ : B₁ pt} {b₂ : B₂ pt} {b₃ : B₃ pt} (f₂ : Πa, B₂ a → B₃ a) (p₂ : f₂ pt b₂ = b₃)
    (f₁ : Πa, B₁ a → B₂ a) (p₁ : f₁ pt b₁ = b₂)
    (g : ppi B₁ b₁) : ppi_functor_right (λa, f₂ a ∘ f₁ a) (ap (f₂ pt) p₁ ⬝ p₂) g ~*
    ppi_functor_right f₂ p₂ (ppi_functor_right f₁ p₁ g) :=
  begin
    fapply phomotopy.mk,
    { reflexivity },
    { induction p₁, induction p₂, exact !idp_con ⬝ !ap_compose⁻¹ }
  end

  definition ppi_functor_right_id [constructor] {A : Type*} {B : A → Type}
    {b : B pt} (g : ppi B b) : ppi_functor_right (λa, id) idp g ~* g :=
  begin
    fapply phomotopy.mk,
    { reflexivity },
    { reflexivity }
  end

  definition ppi_functor_right_phomotopy [constructor] {g g' : Π(a : A), B a → C a}
    {g₀ : g pt b₀ = c₀} {g₀' : g' pt b₀ = c₀} {f f' : ppi B b₀}
    (p : g ~2 g') (q : f ~* f') (r : p pt b₀ ⬝ g₀' = g₀) :
    ppi_functor_right g g₀ f ~* ppi_functor_right g' g₀' f' :=
  phomotopy.mk (λa, p a (f a) ⬝ ap (g' a) (q a))
    abstract begin
      induction q using phomotopy_rec_idp,
      induction r, revert g p, refine rec_idp_of_equiv _ homotopy2.rfl _ _ _,
      { intro h h', exact !eq_equiv_eq_symm ⬝e !eq_equiv_homotopy2 },
      { reflexivity },
      induction g₀', induction f with f f₀, induction f₀, reflexivity
    end end

  definition ppi_functor_right_phomotopy_refl [constructor] (g : Π(a : A), B a → C a)
    (g₀ : g pt b₀ = c₀) (f : ppi B b₀) :
    ppi_functor_right_phomotopy (homotopy2.refl g) (phomotopy.refl f) !idp_con =
    phomotopy.refl (ppi_functor_right g g₀ f) :=
  begin
    induction g₀,
    apply ap (phomotopy.mk homotopy.rfl),
    refine !phomotopy_rec_idp_refl ⬝ _,
    esimp,
    refine !rec_idp_of_equiv_idp ⬝ _,
    induction f with f f₀, induction f₀, reflexivity
  end

  definition ppi_equiv_ppi_right [constructor] {A : Type*} {B B' : A → Type}
    {b : B pt} {b' : B' pt} (f : Πa, B a ≃ B' a) (p : f pt b = b') :
    ppi B b ≃ ppi B' b' :=
  equiv.MK (ppi_functor_right f p) (ppi_functor_right (λa, (f a)⁻¹ᵉ) (inv_eq_of_eq p⁻¹))
    abstract begin
      intro g, apply eq_of_phomotopy,
      refine !ppi_functor_right_compose⁻¹* ⬝* _,
      refine ppi_functor_right_phomotopy (λa, to_right_inv (f a)) (phomotopy.refl g) _ ⬝*
            !ppi_functor_right_id, induction p, exact adj (f pt) b ⬝ ap02 (f pt) !idp_con⁻¹

    end end
    abstract begin
      intro g, apply eq_of_phomotopy,
      refine !ppi_functor_right_compose⁻¹* ⬝* _,
      refine ppi_functor_right_phomotopy (λa, to_left_inv (f a)) (phomotopy.refl g) _ ⬝*
            !ppi_functor_right_id, induction p, exact (!idp_con ⬝ !idp_con)⁻¹,
    end end

  definition ppi_equiv_ppi_basepoint [constructor] {A : Type*} {B : A → Type} {b b' : B pt}
    (p : b = b') : ppi B b ≃ ppi B b' :=
  ppi_equiv_ppi_right (λa, erfl) p

  definition pmap_compose_ppi [constructor] (g : Π(a : A), ppmap (P a) (Q a))
    (f : Π*(a : A), P a) : Π*(a : A), Q a :=
  ppi_functor_right g (respect_pt (g pt)) f

  definition ppi_compose_pmap [constructor] (g : Π*(a : A), P a) (f : A' →* A) :
    Π*(a' : A'), P (f a') :=
  ppi.mk (λa', g (f a'))
    (eq_of_pathover_idp  (change_path !con.right_inv
      (apd g (respect_pt f) ⬝op respect_pt g ⬝o (apd (λx, Point (P x)) (respect_pt f))⁻¹ᵒ)))
(* alternate proof for respecting the point -/
-- (eq_tr_of_pathover (apd g (respect_pt f)) ⬝ ap (transport _ _) (respect_pt g) ⬝
--            apdt (λx, Point (P x)) (respect_pt f)⁻¹)

  definition ppi_compose_pmap_phomotopy [constructor] (g : A →* A'') (f : A' →* A) :
    ppi_compose_pmap g f ~* g ∘* f :=
  begin
    refine phomotopy.mk homotopy.rfl _,
    refine !idp_con ⬝ _, esimp,
    symmetry,
    refine !eq_of_pathover_idp_constant ⬝ _,
    refine !eq_of_pathover_change_path ⬝ !eq_of_pathover_cono ⬝ _,
    refine (!eq_of_pathover_concato_eq ⬝ !apd_eq_ap ◾ idp) ◾
           (!eq_of_pathover_invo ⬝ (!apd_eq_ap ⬝ !ap_constant)⁻²) ⬝ _,
    reflexivity
  end

  definition pmap_compose_ppi_ppi_const [constructor] (g : Π(a : A), ppmap (P a) (Q a)) :
    pmap_compose_ppi g (ppi_const P) ~* ppi_const Q :=
  proof phomotopy.mk (λa, respect_pt (g a)) !idp_con⁻¹ qed

  definition pmap_compose_ppi_pconst [constructor] (f : Π*(a : A), P a) :
    pmap_compose_ppi (λa, pconst (P a) (Q a)) f ~* ppi_const Q :=
  phomotopy.mk homotopy.rfl !ap_constant⁻¹

  definition ppi_compose_pmap_ppi_const [constructor] (f : A' →* A) :
    ppi_compose_pmap (ppi_const P) f ~* ppi_const (P ∘ f) :=
  phomotopy.mk homotopy.rfl
    begin
      exact (ap eq_of_pathover_idp (change_path_of_pathover _ _ _ !cono.right_inv))⁻¹,
    end

  definition ppi_compose_pmap_pconst [constructor] (g : Π*(a : A), P a) :
    ppi_compose_pmap g (pconst A' A) ~* pconst A' (P pt) :=
  phomotopy.mk (λa, respect_pt g) !idpo_concato_eq⁻¹

  definition pmap_compose_ppi2 [constructor] {g g' : Π(a : A), ppmap (P a) (Q a)}
    {f f' : Π*(a : A), P a} (p : Πa, g a ~* g' a) (q : f ~* f') :
    pmap_compose_ppi g f ~* pmap_compose_ppi g' f' :=
  ppi_functor_right_phomotopy p q (to_homotopy_pt (p pt))

  definition pmap_compose_ppi2_refl [constructor] (g : Π(a : A), P a →* Q a) (f : Π*(a : A), P a) :
    pmap_compose_ppi2 (λa, phomotopy.refl (g a)) (phomotopy.refl f) = phomotopy.rfl :=
  begin
    refine _ ⬝ ppi_functor_right_phomotopy_refl g (respect_pt (g pt)) f,
    exact ap (ppi_functor_right_phomotopy _ _) (to_right_inv !eq_con_inv_equiv_con_eq _)
  end

  definition pmap_compose_ppi_phomotopy_left [constructor] {g g' : Π(a : A), ppmap (P a) (Q a)}
    (f : Π*(a : A), P a) (p : Πa, g a ~* g' a) : pmap_compose_ppi g f ~* pmap_compose_ppi g' f :=
  pmap_compose_ppi2 p phomotopy.rfl

  definition pmap_compose_ppi_phomotopy_right [constructor] (g : Π(a : A), ppmap (P a) (Q a))
    {f f' : Π*(a : A), P a} (p : f ~* f') : pmap_compose_ppi g f ~* pmap_compose_ppi g f' :=
  pmap_compose_ppi2 (λa, phomotopy.rfl) p

  definition pmap_compose_ppi_pid_left [constructor]
    (f : Π*(a : A), P a) : pmap_compose_ppi (λa, pid (P a)) f ~* f :=
  phomotopy.mk homotopy.rfl idp

  definition pmap_compose_ppi_pcompose [constructor] (h : Π(a : A), ppmap (Q a) (R a))
    (g : Π(a : A), ppmap (P a) (Q a)) :
    pmap_compose_ppi (λa, h a ∘* g a) f ~* pmap_compose_ppi h (pmap_compose_ppi g f)  :=
  phomotopy.mk homotopy.rfl
    abstract !idp_con ⬝ whisker_right _ (!ap_con ⬝ whisker_right _ !ap_compose') ⬝ !con.assoc end

  definition ppi_assoc [constructor] (h : Π (a : A), Q a →* R a) (g : Π (a : A), P a →* Q a)
    (f : Π*a, P a) :
    pmap_compose_ppi (λa, h a ∘* g a) f ~* pmap_compose_ppi h (pmap_compose_ppi g f) :=
  begin
    fapply phomotopy.mk,
    { intro a, reflexivity },
    exact !idp_con ⬝ whisker_right _ (!ap_con ⬝ whisker_right _ !ap_compose⁻¹) ⬝ !con.assoc
  end

  definition pmap_compose_ppi_eq_of_phomotopy (g : Πa, P a →* Q a) {f f' : Π*a, P a} (p : f ~* f') :
    ap (pmap_compose_ppi g) (eq_of_phomotopy p) =
    eq_of_phomotopy (pmap_compose_ppi_phomotopy_right g p) :=
  begin
    induction p using phomotopy_rec_idp,
    refine ap02 _ !eq_of_phomotopy_refl ⬝ !eq_of_phomotopy_refl⁻¹ ⬝ ap eq_of_phomotopy _,
    exact !pmap_compose_ppi2_refl⁻¹
  end

  definition ppi_assoc_ppi_const_right (g : Πa, Q a →* R a) (f : Πa, P a →* Q a) :
    ppi_assoc g f (ppi_const P) ⬝*
    (pmap_compose_ppi_phomotopy_right _ (pmap_compose_ppi_ppi_const f) ⬝*
    pmap_compose_ppi_ppi_const g) = pmap_compose_ppi_ppi_const (λa, g a ∘* f a) :=
  begin
    revert R g, refine fiberwise_pointed_map_rec _ _,
    revert Q f, refine fiberwise_pointed_map_rec _ _,
    intro Q f R g,
    refine ap (λx, _ ⬝* (x ⬝* _)) !pmap_compose_ppi2_refl ⬝ _,
    reflexivity
  end

  definition pppi_compose_left [constructor] (g : Π(a : A), ppmap (P a) (Q a)) :
    (Π*(a : A), P a) →* Π*(a : A), Q a :=
  pmap.mk (pmap_compose_ppi g) (eq_of_phomotopy (pmap_compose_ppi_ppi_const g))

  definition pppi_compose_right [constructor] (f : A' →* A) :
    (Π*(a : A), P a) →* Π*(a' : A'), P (f a') :=
  pmap.mk (λh, ppi_compose_pmap h f) (eq_of_phomotopy (ppi_compose_pmap_ppi_const f))

  definition pppi_compose_right_phomotopy [constructor] (f : A' →* A) :
    pppi_compose_right f ~* @ppcompose_right _ _ A'' f :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro g, exact ppi_compose_pmap_phomotopy g f },
    { exact sorry }
  end

  -- pppi_compose_left is a functor in the following sense
  definition pppi_compose_left_pcompose (g : Π (a : A), Q a →* R a) (f : Π (a : A), P a →* Q a)
    : pppi_compose_left (λ a, g a ∘* f a) ~* (pppi_compose_left g ∘* pppi_compose_left f) :=
  begin
    fapply phomotopy_mk_ppi,
    { exact ppi_assoc g f },
    { refine idp ◾** (!phomotopy_of_eq_con ⬝
        (ap phomotopy_of_eq !pmap_compose_ppi_eq_of_phomotopy ⬝ !phomotopy_of_eq_of_phomotopy) ◾**
        !phomotopy_of_eq_of_phomotopy) ⬝ _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹,
      apply ppi_assoc_ppi_const_right },
  end

  definition pppi_compose_left_phomotopy [constructor] {g g' : Π(a : A), ppmap (P a) (Q a)}
    (p : Πa, g a ~* g' a) : pppi_compose_left g ~* pppi_compose_left g' :=
  begin
    apply phomotopy_of_eq, apply ap pppi_compose_left, apply eq_of_homotopy, intro a,
    apply eq_of_phomotopy, exact p a
  end

  definition psquare_pppi_compose_left {A : Type*} {B C D E : A → Type*}
    {ftop : Π (a : A), B a →* C a} {fbot : Π (a : A), D a →* E a}
    {fleft : Π (a : A), B a →* D a} {fright : Π (a : A), C a →* E a}
    (psq : Π (a :A), psquare (ftop a) (fbot a) (fleft a) (fright a))
    : psquare
        (pppi_compose_left ftop)
        (pppi_compose_left fbot)
        (pppi_compose_left fleft)
        (pppi_compose_left fright)
    :=
  begin
    refine (pppi_compose_left_pcompose fright ftop)⁻¹* ⬝* _ ⬝*
           (pppi_compose_left_pcompose fbot fleft),
    exact pppi_compose_left_phomotopy psq
  end

  definition ppi_pequiv_right [constructor] (g : Π(a : A), P a ≃* Q a) :
    (Π*(a : A), P a) ≃* Π*(a : A), Q a :=
  begin
    apply pequiv_of_pmap (pppi_compose_left g),
    apply adjointify _ (pppi_compose_left (λa, (g a)⁻¹ᵉ*)),
    { intro f, apply eq_of_phomotopy,
      refine !pmap_compose_ppi_pcompose⁻¹* ⬝* _,
      refine pmap_compose_ppi_phomotopy_left _ (λa, !pright_inv) ⬝* _,
      apply pmap_compose_ppi_pid_left },
    { intro f, apply eq_of_phomotopy,
      refine !pmap_compose_ppi_pcompose⁻¹* ⬝* _,
      refine pmap_compose_ppi_phomotopy_left _ (λa, !pleft_inv) ⬝* _,
      apply pmap_compose_ppi_pid_left }
  end

end pointed


namespace pointed

  variables {A B C : Type*}

  -- TODO: replace in types.fiber
  definition pfiber.sigma_char' (f : A →* B) :
    pfiber f ≃* psigma_gen (λa, f a = pt) (respect_pt f) :=
  pequiv_of_equiv (fiber.sigma_char f pt) idp

  definition fiberpt [constructor] {A B : Type*} {f : A →* B} : fiber f pt :=
  fiber.mk pt (respect_pt f)

  definition psigma_fiber_pequiv [constructor] {A B : Type*} (f : A →* B) :
    psigma_gen (fiber f) fiberpt ≃* A :=
  pequiv_of_equiv (sigma_fiber_equiv f) idp

  definition ppmap.sigma_char [constructor] (A B : Type*) :
    ppmap A B ≃* @psigma_gen (A →ᵘ* B) (λf, f pt = pt) idp :=
  pequiv_of_equiv !pmap.sigma_char idp

  definition pppi.sigma_char [constructor] (B : A → Type*) :
    (Π*(a : A), B a) ≃* @psigma_gen (Πᵘ*a, B a) (λf, f pt = pt) idp :=
  proof pequiv_of_equiv !ppi.sigma_char idp qed

  definition pppi_sigma_char_natural_bottom [constructor] {B B' : A → Type*} (f : Πa, B a →* B' a) :
    @psigma_gen (Πᵘ*a, B a) (λg, g pt = pt) idp →* @psigma_gen (Πᵘ*a, B' a) (λg, g pt = pt) idp :=
  psigma_gen_functor
    (pupi_functor_right f)
    (λg p, ap (f pt) p ⬝ respect_pt (f pt))
    begin
      apply eq_pathover_constant_right, apply square_of_eq,
      esimp, exact !idp_con ⬝ !apd10_eq_of_homotopy⁻¹ ⬝ !ap_eq_apd10⁻¹,
    end

  definition pppi_sigma_char_natural {B B' : A → Type*} (f : Πa, B a →* B' a) :
    psquare (pppi_compose_left f) (pppi_sigma_char_natural_bottom f)
            (pppi.sigma_char B) (pppi.sigma_char B') :=
  begin
    fapply phomotopy.mk,
    { intro g, reflexivity },
    { refine !idp_con ⬝ !idp_con ⬝ _,
      fapply sigma_eq2,
      { refine !sigma_eq_pr1 ⬝ _ ⬝ !ap_sigma_pr1⁻¹,
        apply inj !eq_equiv_homotopy,
        refine !apd10_eq_of_homotopy_fn ⬝ _ ⬝ !apd10_to_fun_eq_of_phomotopy⁻¹,
        apply eq_of_homotopy, intro a, reflexivity },
      { exact sorry } }
  end

  open sigma.ops

  definition psigma_gen_pi_pequiv_pupi_psigma_gen [constructor] {A : Type*} {B : A → Type*}
    (C : Πa, B a → Type) (c : Πa, C a pt) :
    @psigma_gen (Πᵘ*a, B a) (λf, Πa, C a (f a)) c ≃* Πᵘ*a, psigma_gen (C a) (c a) :=
  pequiv_of_equiv sigma_pi_equiv_pi_sigma idp

  definition pupi_psigma_gen_pequiv_psigma_gen_pi [constructor] {A : Type*} {B : A → Type*}
    (C : Πa, B a → Type) (c : Πa, C a pt) :
    (Πᵘ*a, psigma_gen (C a) (c a)) ≃* @psigma_gen (Πᵘ*a, B a) (λf, Πa, C a (f a)) c :=
  pequiv_of_equiv sigma_pi_equiv_pi_sigma⁻¹ᵉ idp

  definition psigma_gen_assoc [constructor] {A : Type*} {B : A → Type} (C : Πa, B a → Type)
    (b₀ : B pt) (c₀ : C pt b₀) :
    psigma_gen (λa, Σb, C a b) ⟨b₀, c₀⟩ ≃* @psigma_gen (psigma_gen B b₀) (λv, C v.1 v.2) c₀ :=
  pequiv_of_equiv !sigma_assoc_equiv' idp

  definition psigma_gen_swap [constructor] {A : Type*} {B B' : A → Type}
    (C : Π⦃a⦄, B a → B' a → Type) (b₀ : B pt) (b₀' : B' pt) (c₀ : C b₀ b₀') :
    @psigma_gen (psigma_gen B  b₀ ) (λv, Σb', C v.2 b') ⟨b₀', c₀⟩ ≃*
    @psigma_gen (psigma_gen B' b₀') (λv, Σb , C b  v.2) ⟨b₀ , c₀⟩ :=
  !psigma_gen_assoc⁻¹ᵉ* ⬝e* psigma_gen_pequiv_psigma_gen_right (λa, !sigma_comm_equiv) idp ⬝e*
  !psigma_gen_assoc

  definition ppi_psigma.{u v w} {A : pType.{u}} {B : A → pType.{v}} (C : Πa, B a → Type.{w})
    (c : Πa, C a pt) : (Π*(a : A), (psigma_gen (C a) (c a))) ≃*
    psigma_gen (λ(f : Π*(a : A), B a), ppi (λa, C a (f a))
                 (transport (C pt) (respect_pt f)⁻¹ (c pt))) (ppi_const _) :=
  proof
  calc (Π*(a : A), psigma_gen (C a) (c a))
          ≃* @psigma_gen (Πᵘ*a, psigma_gen (C a) (c a)) (λf, f pt = pt) idp : pppi.sigma_char
      ... ≃* @psigma_gen (@psigma_gen (Πᵘ*a, B a) (λf, Πa, C a (f a)) c)
                         (λv, Σ(p : v.1 pt = pt), v.2 pt =[p] c pt) ⟨idp, idpo⟩ :
             by exact psigma_gen_pequiv_psigma_gen (pupi_psigma_gen_pequiv_psigma_gen_pi C c)
                        (λf, sigma_eq_equiv _ _) idpo
      ... ≃* @psigma_gen (@psigma_gen (Πᵘ*a, B a) (λf, f pt = pt) idp)
                         (λv, Σ(g : Πa, C a (v.1 a)), g pt =[v.2] c pt) ⟨c, idpo⟩ :
             by apply psigma_gen_swap
      ... ≃* psigma_gen (λ(f : Π*(a : A), B a), ppi (λa, C a (f a))
                                                        (transport (C pt) (respect_pt f)⁻¹ (c pt)))
                        (ppi_const _) :
             by exact (psigma_gen_pequiv_psigma_gen (pppi.sigma_char B)
                (λf, !ppi.sigma_char ⬝e sigma_equiv_sigma_right (λg, !pathover_equiv_eq_tr⁻¹ᵉ))
                idpo)⁻¹ᵉ*
  qed

  definition ppmap_psigma {A B : Type*} (C : B → Type) (c : C pt) :
    ppmap A (psigma_gen C c) ≃*
    psigma_gen (λ(f : ppmap A B), ppi (C ∘ f) (transport C (respect_pt f)⁻¹ c))
                (ppi_const _) :=
  !pppi_pequiv_ppmap⁻¹ᵉ* ⬝e* !ppi_psigma ⬝e*
  sorry
--  psigma_gen_pequiv_psigma_gen (pppi_pequiv_ppmap A B) (λf, begin esimp, exact ppi_equiv_ppi_right (λa, _) _ end) _

  definition pfiber_pppi_compose_left {B C : A → Type*} (f : Πa, B a →* C a) :
    pfiber (pppi_compose_left f) ≃* Π*(a : A), pfiber (f a) :=
  calc
    pfiber (pppi_compose_left f) ≃*
             psigma_gen (λ(g : Π*(a : A), B a), pmap_compose_ppi f g = ppi_const C)
               proof (eq_of_phomotopy (pmap_compose_ppi_ppi_const f)) qed :
            by exact !pfiber.sigma_char'
      ... ≃* psigma_gen (λ(g : Π*(a : A), B a), pmap_compose_ppi f g ~* ppi_const C)
               proof (pmap_compose_ppi_ppi_const f) qed :
             by exact psigma_gen_pequiv_psigma_gen_right (λa, !ppi_eq_equiv)
                        !phomotopy_of_eq_of_phomotopy
      ... ≃* @psigma_gen (Π*(a : A), B a) (λ(g : Π*(a : A), B a), ppi (λa, f a (g a) = pt)
               (transport (λb, f pt b = pt) (respect_pt g)⁻¹ (respect_pt (f pt))))
               (ppi_const _) :
             begin
               refine psigma_gen_pequiv_psigma_gen_right
                        (λg, ppi_equiv_ppi_basepoint (_ ⬝ !eq_transport_Fl⁻¹)) _,
               intro g, refine !con_idp ⬝ _, apply whisker_right,
               exact ap02 (f pt) !inv_inv⁻¹ ⬝ !ap_inv,
               apply eq_of_phomotopy, fapply phomotopy.mk,
                 intro x, reflexivity,
                 refine !idp_con ⬝ _, symmetry, refine !ap_id ◾ !idp_con ⬝ _, apply con.right_inv
             end
      ... ≃* Π*(a : A), (psigma_gen (λb, f a b = pt) (respect_pt (f a))) :
            by exact (ppi_psigma _ _)⁻¹ᵉ*
      ... ≃* Π*(a : A), pfiber (f a) : by exact ppi_pequiv_right (λa, !pfiber.sigma_char'⁻¹ᵉ*)

  (* TODO: proof the following as a special case of pfiber_pppi_compose_left -/
  definition pfiber_ppcompose_left (f : B →* C) :
    pfiber (@ppcompose_left A B C f) ≃* ppmap A (pfiber f) :=
  calc
    pfiber (@ppcompose_left A B C f) ≃*
             psigma_gen (λ(g : ppmap A B), f ∘* g = pconst A C)
             proof (eq_of_phomotopy (pcompose_pconst f)) qed :
             by exact !pfiber.sigma_char'
      ... ≃* psigma_gen (λ(g : ppmap A B), f ∘* g ~* pconst A C) proof (pcompose_pconst f) qed :
             by exact psigma_gen_pequiv_psigma_gen_right (λa, !pmap_eq_equiv)
                        !phomotopy_of_eq_of_phomotopy
      ... ≃* psigma_gen (λ(g : ppmap A B), ppi (λa, f (g a) = pt)
               (transport (λb, f b = pt) (respect_pt g)⁻¹ (respect_pt f)))
               (ppi_const _) :
             begin
               refine psigma_gen_pequiv_psigma_gen_right
                        (λg, ppi_equiv_ppi_basepoint (_ ⬝ !eq_transport_Fl⁻¹)) _,
               intro g, refine !con_idp ⬝ _, apply whisker_right,
               exact ap02 f !inv_inv⁻¹ ⬝ !ap_inv,
               apply eq_of_phomotopy, fapply phomotopy.mk,
                 intro x, reflexivity,
                 refine !idp_con ⬝ _, symmetry, refine !ap_id ◾ !idp_con ⬝ _, apply con.right_inv
             end
      ... ≃* ppmap A (psigma_gen (λb, f b = pt) (respect_pt f)) :
             by exact (ppmap_psigma _ _)⁻¹ᵉ*
      ... ≃* ppmap A (pfiber f) : by exact ppmap_pequiv_ppmap_right !pfiber.sigma_char'⁻¹ᵉ*

  -- definition pppi_ppmap {A C : Type*} {B : A → Type*} :
  --   ppmap ((* dependent smash of B -/) C ≃* Π*(a : A), ppmap (B a) C :=

  definition ppi_add_point_over {A : Type} (B : A → Type*) :
    (Π*a, add_point_over B a) ≃ Πa, B a :=
  begin
    fapply equiv.MK,
    { intro f a, exact f (some a) },
    { intro f, fconstructor,
        intro a, cases a, exact pt, exact f a,
        reflexivity },
    { intro f, reflexivity },
    { intro f, cases f with f p, apply eq_of_phomotopy, fapply phomotopy.mk,
      { intro a, cases a, exact p⁻¹, reflexivity },
      { exact con.left_inv p }},
  end

  definition pppi_add_point_over {A : Type} (B : A → Type*) :
    (Π*a, add_point_over B a) ≃* Πᵘ*a, B a :=
  pequiv_of_equiv (ppi_add_point_over B) idp

  definition ppmap_add_point {A : Type} (B : Type*) :
    ppmap A₊ B ≃* A →ᵘ* B :=
  pequiv_of_equiv (pmap_equiv_left A B) idp

  (* There are some lemma's needed to prove the naturality of the equivalence
     Ω (Π*a, B a) ≃* Π*(a : A), Ω (B a) -/
  definition ppi_eq_equiv_natural_gen_lem {B C : A → Type} {b₀ : B pt} {c₀ : C pt}
    {f : Π(a : A), B a → C a} {f₀ : f pt b₀ = c₀} {k : ppi B b₀} {k' : ppi C c₀}
    (p : ppi_functor_right f f₀ k ~* k') :
    ap1_gen (f pt) (p pt) f₀ (respect_pt k) = respect_pt k' :=
  begin
    symmetry,
    refine _ ⬝ !con.assoc⁻¹,
    exact eq_inv_con_of_con_eq (to_homotopy_pt p),
  end

  definition ppi_eq_equiv_natural_gen_lem2 {B C : A → Type} {b₀ : B pt} {c₀ : C pt}
    {f : Π(a : A), B a → C a} {f₀ : f pt b₀ = c₀} {k l : ppi B b₀}
    {k' l' : ppi C c₀} (p : ppi_functor_right f f₀ k ~* k')
    (q : ppi_functor_right f f₀ l ~* l') :
      ap1_gen (f pt) (p pt) (q pt) (respect_pt k ⬝ (respect_pt l)⁻¹) =
      respect_pt k' ⬝ (respect_pt l')⁻¹ :=
  (ap1_gen_con (f pt) _ f₀ _ _ _ ⬝ (ppi_eq_equiv_natural_gen_lem p) ◾
  (!ap1_gen_inv ⬝ (ppi_eq_equiv_natural_gen_lem q)⁻²))

  definition ppi_eq_equiv_natural_gen {B C : A → Type} {b₀ : B pt} {c₀ : C pt}
    {f : Π(a : A), B a → C a} {f₀ : f pt b₀ = c₀} {k l : ppi B b₀}
    {k' l' : ppi C c₀} (p : ppi_functor_right f f₀ k ~* k')
    (q : ppi_functor_right f f₀ l ~* l') :
    hsquare (ap1_gen (ppi_functor_right f f₀) (eq_of_phomotopy p) (eq_of_phomotopy q))
            (ppi_functor_right (λa, ap1_gen (f a) (p a) (q a))
              (ppi_eq_equiv_natural_gen_lem2 p q))
            phomotopy_of_eq
            phomotopy_of_eq :=
  begin
    intro r, induction r,
    induction f₀,
    induction k with k k₀,
    induction k₀,
    refine idp ⬝ _,
    revert l' q, refine phomotopy_rec_idp' _ _,
    revert k' p, refine phomotopy_rec_idp' _ _,
    reflexivity
  end

  definition ppi_eq_equiv_natural_gen_refl {B C : A → Type}
    {f : Π(a : A), B a → C a} {k : Πa, B a} :
    ppi_eq_equiv_natural_gen (phomotopy.refl (ppi_functor_right f idp (ppi.mk k idp)))
      (phomotopy.refl (ppi_functor_right f idp (ppi.mk k idp))) idp =
    ap phomotopy_of_eq !ap1_gen_idp :=
  begin
    refine !idp_con ⬝ _,
    refine !phomotopy_rec_idp'_refl ⬝ _,
    refine ap (transport _ _) !phomotopy_rec_idp'_refl ⬝ _,
    refine !tr_diag_eq_tr_tr⁻¹ ⬝ _,
    refine !eq_transport_Fl ⬝ _,
    refine !ap_inv⁻² ⬝ !inv_inv ⬝ !ap_compose ⬝ ap02 _ _,
    exact !ap1_gen_idp_eq⁻¹
  end

  definition loop_pppi_pequiv [constructor] {A : Type*} (B : A → Type*) :
    Ω (Π*a, B a) ≃* Π*(a : A), Ω (B a) :=
  pequiv_of_equiv !ppi_eq_equiv idp

  definition loop_pppi_pequiv_natural_right {A : Type*} {X Y : A → Type*}
    (f :  Π (a : A), X a →* Y a) :
    psquare (loop_pppi_pequiv X)
            (loop_pppi_pequiv Y)
            (Ω→ (pppi_compose_left f))
            (pppi_compose_left (λ a, Ω→ (f a))) :=
  begin
    apply ptranspose,
    revert Y f, refine fiberwise_pointed_map_rec _ _, intro Y f,
    fapply phomotopy.mk,
    { exact ppi_eq_equiv_natural_gen (pmap_compose_ppi_ppi_const (λa, pmap_of_map (f a) pt))
              (pmap_compose_ppi_ppi_const (λa, pmap_of_map (f a) pt)) },
    { exact !ppi_eq_equiv_natural_gen_refl ◾ (!idp_con ⬝ !eq_of_phomotopy_refl) }
  end

  definition loop_pppi_pequiv_natural_left {A B : Type*} {X : A → Type*} (f : B →* A) :
    psquare (loop_pppi_pequiv X)
            (loop_pppi_pequiv (X ∘ f))
            (Ω→ (pppi_compose_right f))
            (pppi_compose_right f) :=
  begin
    exact sorry
  end

  definition loopn_pppi_pequiv (n : ℕ) {A : Type*} (B : A → Type*) :
    Ω[n] (Π*a, B a) ≃* Π*(a : A), Ω[n] (B a) :=
  begin
    induction n with n IH,
    { reflexivity },
    { refine loop_pequiv_loop IH ⬝e* loop_pppi_pequiv (λa, Ω[n] (B a)) }
  end

  definition loop_ppmap_pequiv [constructor] (A B : Type*) : Ω (A →** B) ≃* A →** Ω B :=
  !loop_pppi_pequiv

  definition loop_ppmap_pequiv_natural_right (A : Type*) {X Y : Type*} (f :  X →* Y) :
    psquare (loop_ppmap_pequiv A X)
            (loop_ppmap_pequiv A Y)
            (Ω→ (ppcompose_left f))
            (ppcompose_left (Ω→ f)) :=
  begin
    exact loop_pppi_pequiv_natural_right (λa, f)
  end

  definition loop_ppmap_pequiv_natural_left {A B : Type*} (X : Type*) (f :  A →* B) :
    psquare (loop_ppmap_pequiv B X)
            (loop_ppmap_pequiv A X)
            (Ω→ (ppcompose_right f))
            (ppcompose_right f) :=
  begin
    refine Ω⇒ !pppi_compose_right_phomotopy⁻¹* ⬝ph* _ ⬝hp* !pppi_compose_right_phomotopy⁻¹*,
    exact loop_pppi_pequiv_natural_left f
  end

  definition loopn_ppmap_pequiv (n : ℕ) (A B : Type*) : Ω[n] (A →** B) ≃* A →** Ω[n] B :=
  !loopn_pppi_pequiv

  definition pfunext [constructor] {A : Type*} (B : A → Type*) :
    (Π*(a : A), Ω (B a)) ≃* Ω (Π*a, B a) :=
  (loop_pppi_pequiv B)⁻¹ᵉ*

definition deloopable_pppi [instance] [constructor] {A : Type*} (B : A → Type*) [Πa, deloopable (B a)] :
  deloopable (Π*a, B a) :=
deloopable.mk (Π*a, deloop (B a))
              (loop_pppi_pequiv (λa, deloop (B a)) ⬝e* ppi_pequiv_right (λa, deloop_pequiv (B a)))

definition deloopable_ppmap [instance] [constructor] (A B : Type*) [deloopable B] :
  deloopable (A →** B) :=
deloopable_pppi (λa, B)


(* below is an alternate proof strategy for the naturality of loop_pppi_pequiv_natural,
  where we define loop_pppi_pequiv as composite of pointed equivalences, and proved the
  naturality individually. That turned out to be harder.
-/

(*  definition loop_pppi_pequiv2 {A : Type*} (B : A → Type*) : Ω (Π*a, B a) ≃* Π*(a : A), Ω (B a) :=
  begin
    refine loop_pequiv_loop (pppi.sigma_char B) ⬝e* _,
    refine !loop_psigma_gen ⬝e* _,
    transitivity @psigma_gen (Πᵘ*a, Ω (B a)) (λf, f pt = idp) idp,
      exact psigma_gen_pequiv_psigma_gen
      (loop_pupi B) (λp, eq_pathover_equiv_Fl p idp idp ⬝e
                  equiv_eq_closed_right _ (whisker_right _ (ap_eq_apd10 p _)) ⬝e !eq_equiv_eq_symm) idpo,
    exact (pppi.sigma_char (Ω ∘ B))⁻¹ᵉ*
  end

  definition loop_pppi_pequiv_natural2 {A : Type*} {X Y : A → Type*} (f :  Π (a : A), X a →* Y a) :
    psquare
      (Ω→ (pppi_compose_left f))
      (pppi_compose_left (λ a, Ω→ (f a)))
      (loop_pppi_pequiv2 X)
      (loop_pppi_pequiv2 Y) :=
  begin
    refine ap1_psquare (pppi_sigma_char_natural f) ⬝v* _,
    refine !loop_psigma_gen_natural ⬝v* _,
    refine _ ⬝v* (pppi_sigma_char_natural (λ a, Ω→ (f a)))⁻¹ᵛ*,
    fapply psigma_gen_functor_psquare,
    { apply loop_pupi_natural },
    { intro p q, exact sorry },
    { exact sorry }
  end-/

end pointed open pointed

open is_trunc is_conn
namespace is_conn
  section

  (* todo: reorder arguments and make some implicit -/
  variables (A : Type*) (n : ℕ₋₂) (H : is_conn (n.+1) A)
  include H

  definition is_contr_ppi_match (P : A → Type*) (H2 : Πa, is_trunc (n.+1) (P a))
    : is_contr (Π*(a : A), P a) :=
  begin
    apply is_contr.mk pt,
    intro f, induction f with f p,
    apply eq_of_phomotopy, fapply phomotopy.mk,
    { apply is_conn.elim n, exact p⁻¹ },
    { krewrite (is_conn.elim_β n), apply con.left_inv }
  end

  -- definition is_trunc_ppi_of_is_conn (k : ℕ₋₂) (P : A → Type*)
  --   : is_trunc k.+1 (Π*(a : A), P a) :=

  definition is_trunc_ppi_of_is_conn (k l : ℕ₋₂) (H2 : l ≤ n.+1+2+k)
    (P : A → Type*) (H3 : Πa, is_trunc l (P a)) :
    is_trunc k.+1 (Π*(a : A), P a) :=
  begin
    have H4 : Πa, is_trunc (n.+1+2+k) (P a), from λa, is_trunc_of_le (P a) H2 _,
    clear H2 H3, revert P H4,
    induction k with k IH: intro P H4,
    { apply is_prop_of_imp_is_contr, intro f,
      apply is_contr_ppi_match A n H P H4 },
    { apply is_trunc_succ_of_is_trunc_loop
        (trunc_index.succ_le_succ (trunc_index.minus_two_le k)),
      intro f,
      apply @is_trunc_equiv_closed_rev _ _ k.+1 (ppi_loop_equiv f),
      apply IH, intro a,
      apply is_trunc_loop, apply H4 }
  end

  definition is_trunc_pmap_of_is_conn (k l : ℕ₋₂) (B : Type*) (H2 : l ≤ n.+1+2+k)
    (H3 : is_trunc l B) : is_trunc k.+1 (A →* B) :=
  is_trunc_ppi_of_is_conn A n H k l H2 (λ a, B) _

  end

  open trunc_index algebra nat
  definition is_trunc_ppi_of_is_conn_nat
    (A : Type*) (n : ℕ) (H : is_conn (n.-1) A) (k l : ℕ) (H2 : l ≤ n + k)
    (P : A → Type*) (H3 : Πa, is_trunc l (P a)) :
    is_trunc k (Π*(a : A), P a) :=
  begin
    refine is_trunc_ppi_of_is_conn A (n.-2) H (k.-1) l _ P H3,
    refine le.trans (of_nat_le_of_nat H2) (le_of_eq !sub_one_add_plus_two_sub_one⁻¹)
  end

  definition is_trunc_pmap_of_is_conn_nat (A : Type*) (n : ℕ) (H : is_conn (n.-1) A) (k l : ℕ)
    (B : Type*) (H2 : l ≤ n + k) (H3 : is_trunc l B) : is_trunc k (A →* B) :=
  is_trunc_ppi_of_is_conn_nat A n H k l H2 (λ a, B) _

  -- this is probably much easier to prove directly
  definition is_trunc_ppi (A : Type*) (n k : ℕ₋₂) (H : n ≤ k) (P : A → Type*)
    (H2 : Πa, is_trunc n (P a)) : is_trunc k (Π*(a : A), P a) :=
  begin
    cases k with k,
    { apply is_contr_of_merely_prop,
      { exact @is_trunc_ppi_of_is_conn A -2 (is_conn_minus_one A (tr pt)) -2 _
                (trunc_index.le.step H) P H2 },
      { exact tr pt } },
    { assert K : n ≤ -1 +2+ k,
      { rewrite (trunc_index.add_plus_two_comm -1 k), exact H },
      { exact @is_trunc_ppi_of_is_conn A -2 (is_conn_minus_one A (tr pt)) k _ K P H2 } }
  end

end is_conn


(* TODO: move, these facts use some of these pointed properties -/

namespace trunc

lemma pmap_ptrunc_pequiv_natural [constructor] (n : ℕ₋₂) {A A' B B' : Type*}
  [H : is_trunc n B] [H : is_trunc n B'] (f : A' →* A) (g : B →* B') :
  psquare (pmap_ptrunc_pequiv n A B) (pmap_ptrunc_pequiv n A' B')
          (ppcompose_left g ∘* ppcompose_right (ptrunc_functor n f))
          (ppcompose_left g ∘* ppcompose_right f) :=
begin
  refine _ ⬝v* _, exact pmap_ptrunc_pequiv n A' B,
  { fapply phomotopy.mk,
    { intro h, apply eq_of_phomotopy,
      exact !passoc ⬝* pwhisker_left h (ptr_natural n f)⁻¹* ⬝* !passoc⁻¹* },
    { xrewrite [▸*, +pcompose_right_eq_of_phomotopy, -+eq_of_phomotopy_trans],
      apply ap eq_of_phomotopy,
      refine !trans_assoc ⬝ idp ◾** (!trans_assoc⁻¹ ⬝ (eq_bot_of_phsquare (phtranspose
               (passoc_pconst_left (ptrunc_functor n f) (ptr n A'))))⁻¹) ⬝ _,
      refine !trans_assoc ⬝ idp ◾** !pconst_pcompose_phomotopy ⬝ _,
      apply passoc_pconst_left }},
  { fapply phomotopy.mk,
    { intro h, apply eq_of_phomotopy, exact !passoc⁻¹* },
    { xrewrite [▸*, pcompose_right_eq_of_phomotopy, pcompose_left_eq_of_phomotopy,
        -+eq_of_phomotopy_trans],
      apply ap eq_of_phomotopy, apply symm_trans_eq_of_eq_trans, symmetry,
      apply passoc_pconst_middle }}
end
end trunc
