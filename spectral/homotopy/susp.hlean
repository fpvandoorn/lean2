import .pushout types.pointed2 ..move_to_lib

open susp eq pointed function is_equiv lift equiv is_trunc nat

namespace susp
  variables {X X' Y Y' Z : pType}

Definition susp_functor_of_fn (f : X -> Y) : susp X ->* susp Y.
  Build_pMap (susp_functor' f) idp
Definition susp_pequiv_of_equiv (f : X <~> Y) : susp X <~>* susp Y.
  pequiv_of_equiv (susp.equiv f) idp

Definition iterate_susp_iterate_susp_rev (n m : ℕ) (A : pType) :
    iterate_susp n (iterate_susp m A) <~>* iterate_susp (m + n) A.
Proof.
    induction n with n e,
    { reflexivity },
    { exact susp_pequiv e }
Defined.

Definition iterate_susp_pequiv (n : ℕ) {X Y : pType} (f : X <~>* Y) :
    iterate_susp n X <~>* iterate_susp n Y.
Proof.
    induction n with n e,
    { exact f },
    { exact susp_pequiv e }
Defined.

  open algebra nat
Definition iterate_susp_iterate_susp (n m : ℕ) (A : pType) :
    iterate_susp n (iterate_susp m A) <~>* iterate_susp (n + m) A.
  iterate_susp_iterate_susp_rev n m A @e* pequiv_of_eq (ap (fun k => iterate_susp k A) (add.comm m n))

Definition plift_susp.{u v} : forall (A : pType), plift.{u v} (susp A) <~>* susp (plift.{u v} A).
Proof.
    intro A,
    calc
      plift.{u v} (susp A) <~>* susp A               : by exact (pequiv_plift (susp A))^-1ᵉ*
                        ... <~>* susp (plift.{u v} A) : by exact susp_pequiv (pequiv_plift.{u v} A)
Defined.

Definition is_contr_susp [instance] (A : Type) [H : is_contr A] : is_contr (susp A).
Proof.
    apply is_contr.mk north,
    intro x, induction x,
    reflexivity,
    exact merid !center,
    apply eq_pathover_constant_left_id_right, apply square_of_eq,
    exact whisker_left idp (ap merid !eq_of_is_contr)
Defined.

Definition loop_susp_pintro_phomotopy {X Y : pType} {f g : ⅀ X ->* Y} (p : f ==* g) :
    loop_susp_pintro X Y f ==* loop_susp_pintro X Y g.
  pwhisker_right (loop_susp_unit X) (Ω⇒ p)

  variables {A₀₀ A₂₀ A₀₂ A₂₂ : pType}
            {f₁₀ : A₀₀ ->* A₂₀} {f₁₂ : A₀₂ ->* A₂₂}
            {f₀₁ : A₀₀ ->* A₀₂} {f₂₁ : A₂₀ ->* A₂₂}

Definition susp_functor_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (⅀-> f₁₀) (⅀-> f₁₂) (⅀-> f₀₁) (⅀-> f₂₁).
  !susp_functor_pcompose^-1* @* susp_functor_phomotopy p @* !susp_functor_pcompose

Definition susp_to_loop_psquare (f₁₀ : A₀₀ ->* A₂₀) (f₁₂ : A₀₂ ->* A₂₂)
    (f₀₁ : susp A₀₀ ->* A₀₂) (f₂₁ : susp A₂₀ ->* A₂₂) : psquare (⅀-> f₁₀) f₁₂ f₀₁ f₂₁ ->
    psquare f₁₀ (Ω-> f₁₂) (loop_susp_pintro A₀₀ A₀₂ f₀₁) (loop_susp_pintro A₂₀ A₂₂ f₂₁).
Proof.
    intro p,
    refine pvconcat _ (ap1_psquare p),
    exact (loop_susp_unit_natural f₁₀)^-1*
Defined.

Definition loop_to_susp_square (f₁₀ : A₀₀ ->* A₂₀) (f₁₂ : A₀₂ ->* A₂₂)
    (f₀₁ : A₀₀ ->* loops A₀₂) (f₂₁ : A₂₀ ->* loops A₂₂) : psquare f₁₀ (Ω-> f₁₂) f₀₁ f₂₁ ->
    psquare (⅀-> f₁₀) f₁₂ (susp_pelim A₀₀ A₀₂ f₀₁) (susp_pelim A₂₀ A₂₂ f₂₁).
Proof.
    intro p,
    refine susp_functor_psquare p @v* _ =>
    exact ptranspose (loop_susp_counit_natural f₁₂)
Defined.

  open pushout unit prod sigma sigma.ops

  section
    parameters {A : pType} {n : ℕ} [HA : is_conn n A]

                parameter (A)
Definition pullback_diagonal_prod_of_wedge : susp (loops A)
      <~> Σ (a : A) (w : wedge A A), prod_of_wedge w = (a, a).
    begin
      refine equiv.trans _
        (comm_equiv_unc (fun z => prod_of_wedge (prod.pr1 z) = (prod.pr2 z, prod.pr2 z))),
      apply equiv.symm,
      apply equiv.trans (sigma_equiv_sigma_right
        (fun w => sigma_equiv_sigma_right
          (fun a => prod_eq_equiv (prod_of_wedge w) (a, a)))),
      apply equiv.trans !pushout.flattening', esimp,
      fapply pushout.equiv
        (fun z => ⟨(point _), z.2⟩) (fun z => ⟨(point _), glue z.1 # z.2⟩) (fun p => star) (fun p => star),
      { apply equiv.trans !sigma_unit_left, fapply equiv.MK,
        { intro z, induction z with a w, induction w with p q, exact p @ q^-1 },
        { intro p, exact ⟨(point _), (p, idp)⟩ },
        { intro p, reflexivity },
        { intro z, induction z with a w, induction w with p q, induction q,
          reflexivity } },
      { fapply equiv.MK,
        { intro z, exact star },
        { intro u, exact ⟨(point _), ⟨(point _), (idp, idp)⟩ ⟩ },
        { intro u, induction u, reflexivity },
        { intro z, induction z with a w, induction w with b z,
          induction z with p q, induction p, esimp at q, induction q,
          reflexivity } },
      { fapply equiv.MK,
        { intro z, exact star },
        { intro u, exact ⟨(point _), ⟨(point _), (idp, idp)⟩ ⟩ },
        { intro u, induction u, reflexivity },
        { intro z, induction z with a w, induction w with b z,
          induction z with p q, induction q, esimp at p, induction p,
          reflexivity } },
      { intro z, induction z with u w, induction u, induction w with a z,
        induction z with p q, reflexivity },
      { intro z, induction z with u w, induction u, induction w with a z,
        induction z with p q, reflexivity }
    end

    parameter {A}
Definition fiber_loop_susp_counit_equiv (a : A)
      : fiber (loop_susp_counit A) a <~> fiber prod_of_wedge (a, a).
    begin
      apply equiv.trans !fiber.sigma_char, apply equiv.trans !pushout.flattening',
      apply equiv.symm, apply equiv.trans !fiber.sigma_char,
      apply equiv.trans (sigma_equiv_sigma_right
        (fun w => prod_eq_equiv (prod_of_wedge w) (a, a))), esimp,
      apply equiv.trans !pushout.flattening',
      esimp,
      fapply pushout.equiv (fun z => ⟨(point _), z.2⟩) (fun z => ⟨(point _), glue z.1 # z.2⟩)
        (fun z => ⟨star, z.2⟩) (fun z => ⟨star, glue z.1 # z.2⟩),
      { fapply equiv.MK,
        { intro w, induction w with u z, induction z with p q,
          exact ⟨q @ p^-1, q⟩ },
        { intro z, induction z with p q, apply dpair star,
          exact (p^-1 @ q, q) },
        { intro z, induction z with p q, esimp, induction q, esimp,
          rewrite [idp_con,inv_inv] },
        { intro w, induction w with u z, induction u, induction z with p q,
          esimp, induction q, rewrite [idp_con,inv_inv] } },
      { fapply equiv.MK,
        { intro w, induction w with b z, induction z with p q, exact ⟨star, q⟩ },
        { intro z, induction z with u p, induction u, esimp at p, esimp,
          apply dpair a, esimp, exact (idp, p) },
        { intro z, induction z with u p, induction u, reflexivity },
        { intro w, induction w with b z, induction z with p q, esimp,
          induction p, reflexivity } },
      { fapply equiv.MK,
        { intro w, induction w with b z, induction z with p q, exact ⟨star, p⟩ },
        { intro z, induction z with u p, induction u, esimp at p, esimp,
          apply dpair a, esimp, exact (p, idp) },
        { intro z, induction z with u p, induction u, reflexivity },
        { intro w, induction w with b z, induction z with p q, esimp,
          induction q, reflexivity } },
      { intro w, induction w with u z, induction u, induction z with p q,
        reflexivity },
      { intro w, induction w with u z, induction u, induction z with p q,
        esimp, induction q, esimp, krewrite prod_transport, fapply sigma_eq,
        { exact idp },
        { esimp, rewrite eq_transport_Fl, rewrite eq_transport_Fl,
          krewrite elim_glue, krewrite [-ap_compose' pr1 prod_of_wedge (glue star)],
          krewrite elim_glue, esimp, apply eq_pathover, rewrite idp_con, esimp,
          apply square_of_eq, rewrite [idp_con,idp_con,inv_inv] } }
    end

    include HA

    open is_conn trunc_index

    parameter (A)
Definition is_conn_fun_loop_susp_counit {k : ℕ} (H : k ≤ 2 * n)
      : is_conn_fun k (loop_susp_counit A).
    begin
      intro a, apply is_conn.is_conn_equiv_closed_rev k (fiber_loop_susp_counit_equiv a),
      fapply @is_conn.is_conn_of_le (fiber prod_of_wedge (a, a)) k (2 * n)
        (of_nat_le_of_nat H),
      assert H : of_nat (2 * n) = of_nat n + of_nat n,
      { rewrite (of_nat_add_of_nat n n), apply ap of_nat,
        apply trans (nat.mul_comm 2 n),
        apply ap (fun k => k + n), exact nat.zero_add n },
      rewrite H,
      exact is_conn_fun_prod_of_wedge n n A A (a => a)
    end
Defined.

Defined. susp
