
import homotopy.EM algebra.category.functor.equivalence types.pointed2 ..pointed_pi ..pointed
  ..move_to_lib .susp ..algebra.exactness ..univalent_subcategory

open eq equiv is_equiv algebra group nat pointed EM.ops is_trunc trunc susp function is_conn nat
universe variable u
(* TODO: try to fix the compilation time of this file *)


namespace EM

Definition EM1_functor_gid (G : Group) : EM1_functor (gid G) ==* !pid.
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x,
  { reflexivity },
  { apply eq_pathover_id_right, apply hdeg_square, apply elim_pth, },
  { apply @is_prop.elim, apply is_trunc_pathover }},
  { reflexivity },
Defined.

Definition EMadd1_functor_gid (G : AbGroup) (n : ℕ) : EMadd1_functor (gid G) n ==* !pid.
Proof.
  induction n with n p,
  { apply EM1_functor_gid } =>
  { refine !EMadd1_functor_succ @* _ =>
  refine ptrunc_functor_phomotopy _ (susp_functor_phomotopy p @* !susp_functor_pid) @* _ =>
  apply ptrunc_functor_pid }
Defined.

Definition EM_functor_gid (G : AbGroup) (n : ℕ) : EM_functor (gid G) n ==* !pid.
Proof.
  cases n with n,
  { apply pmap_of_homomorphism_gid },
  { apply EMadd1_functor_gid }
Defined.

Definition EM1_functor_gcompose {G H K : Group} (ψ : H ->g K) (φ : G ->g H) :
  EM1_functor (ψ og φ) ==* EM1_functor ψ o* EM1_functor φ.
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x,
  { reflexivity },
  { apply eq_pathover, apply hdeg_square, esimp,
  refine !elim_pth @ _ @ (ap_compose (EM1_functor ψ) _ _)^-1 =>
  refine _ @ ap02 _ !elim_pth^-1, exact !elim_pth^-1 },
  { apply @is_prop.elim, apply is_trunc_pathover }},
  { reflexivity },
Defined.

Definition EMadd1_functor_gcompose {G H K : AbGroup} (ψ : H ->g K) (φ : G ->g H) (n : ℕ) :
  EMadd1_functor (ψ og φ) n ==* EMadd1_functor ψ n o* EMadd1_functor φ n.
Proof.
  induction n with n p,
  { apply EM1_functor_gcompose } =>
  { refine !EMadd1_functor_succ @* _ =>
  refine ptrunc_functor_phomotopy _ (susp_functor_phomotopy p @* !susp_functor_pcompose) @* _ =>
  apply ptrunc_functor_pcompose }
Defined.

Definition EM_functor_gcompose {G H K : AbGroup} (ψ : H ->g K) (φ : G ->g H) (n : ℕ) :
  EM_functor (ψ og φ) n ==* EM_functor ψ n o* EM_functor φ n.
Proof.
  cases n with n,
  { apply pmap_of_homomorphism_gcompose },
  { apply EMadd1_functor_gcompose }
Defined.

Definition EM1_functor_phomotopy {G H : Group} {φ ψ : G ->g H} (p : φ == ψ) :
  EM1_functor φ ==* EM1_functor ψ.
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x,
  { reflexivity },
  { apply eq_pathover, apply hdeg_square, esimp,
  refine !elim_pth @ _ @ !elim_pth^-1, exact ap pth (p g) },
  { apply @is_prop.elim, apply is_trunc_pathover }},
  { reflexivity },
Defined.

Definition EMadd1_functor_phomotopy {G H : AbGroup} {φ ψ : G ->g H} (p : φ == ψ) (n : ℕ) :
  EMadd1_functor φ n ==* EMadd1_functor ψ n.
Proof.
  induction n with n q,
  { exact EM1_functor_phomotopy p } =>
  { exact ptrunc_functor_phomotopy _ (susp_functor_phomotopy q) }
Defined.

Definition EM_functor_phomotopy {G H : AbGroup} {φ ψ : G ->g H} (p : φ == ψ) (n : ℕ) :
  EM_functor φ n ==* EM_functor ψ n.
Proof.
  cases n with n,
  { exact pmap_of_homomorphism_phomotopy p },
  { exact EMadd1_functor_phomotopy p n }
Defined.

Definition EM_equiv_EM {G H : AbGroup} (φ : G <~>g H) (n : ℕ) : K G n <~>* K H n.
Proof.
  fapply pequiv.MK',
  { exact EM_functor φ n } =>
  { exact EM_functor φ^-1ᵍ n } =>
  { intro x, refine (EM_functor_gcompose φ^-1ᵍ φ n)^-1* x @ _ =>
  refine _ @ EM_functor_gid G n x =>
  refine EM_functor_phomotopy _ n x =>
  rexact left_inv φ },
  { intro x, refine (EM_functor_gcompose φ φ^-1ᵍ n)^-1* x @ _ =>
  refine _ @ EM_functor_gid H n x =>
  refine EM_functor_phomotopy _ n x =>
  rexact right_inv φ }
Defined.

Definition is_equiv_EM_functor {G H : AbGroup} (φ : G ->g H) [H2 : is_equiv φ]
  (n : ℕ) : is_equiv (EM_functor φ n).
  to_is_equiv (EM_equiv_EM (isomorphism.mk φ H2) n)

Definition fundamental_group_EM1' (G : Group) : G <~>g forall ₁ (EM1 G).
  (fundamental_group_EM1 G)^-1ᵍ

Definition ghomotopy_group_EMadd1' (G : AbGroup) (n : ℕ) : G <~>g forall g[n+1] (EMadd1 G n).
Proof.
  change G <~>g forall ₁ (Ω[n] (EMadd1 G n)),
  refine _ @g homotopy_group_isomorphism_of_pequiv 0 (loopn_EMadd1_pequiv_EM1 G n),
  apply fundamental_group_EM1'
Defined.

Definition homotopy_group_functor_EM1_functor {G H : Group} (φ : G ->g H) :
  forall ->g[1] (EM1_functor φ) o fundamental_group_EM1' G == fundamental_group_EM1' H o φ.
Proof.
  intro g, apply ap tr, exact (concat_1p _) @ !elim_pth,
Defined.

  section

Definition ghomotopy_group_EMadd1'_0 (G : AbGroup) :
  ghomotopy_group_EMadd1' G 0 == fundamental_group_EM1' G.
Proof.
  refine _ @hty id_compose _,
  unfold [ghomotopy_group_EMadd1'],
  apply hwhisker_right (fundamental_group_EM1' G) =>
  refine _ @hty trunc_functor_id _ _ =>
  exact trunc_functor_homotopy _ ap1_pid =>
Defined.

Definition loopn_EMadd1_pequiv_EM1_succ (G : AbGroup) (n : ℕ) :
  loopn_EMadd1_pequiv_EM1 G (succ n) ==* (loopn_succ_in n (EMadd1 G (succ n)))^-1ᵉ* o*
  Ω->[n] (loop_EMadd1 G n) o* loopn_EMadd1_pequiv_EM1 G n.
  by reflexivity


Definition loop_EMadd1_succ (G : AbGroup) (n : ℕ) :
  loop_EMadd1 G (n+1) ==* (loop_ptrunc_pequiv (n+1+1) (susp (EMadd1 G (n+1))))^-1ᵉ* o*
  freudenthal_pequiv (add_mul_le_mul_add n 1 1) (EMadd1 G (n+1)) o*
  (ptrunc_pequiv (n+1+1) (EMadd1 G (n+1)))^-1ᵉ*.
  by reflexivity

Definition loop_EMadd1_natural {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
  psquare (loop_EMadd1 G n) (loop_EMadd1 H n)
  (EMadd1_functor φ n) (Ω-> (EMadd1_functor φ (succ n))).
Proof.
  refine _ @hp* Ω⇒ !EMadd1_functor_succ =>
  induction n with n IH,
  { refine !hopf.to_pmap_delooping_pinv @pv* _ @vp* !hopf.to_pmap_delooping_pinv,
  exact !loop_susp_unit_natural @h* ap1_psquare !ptr_natural },
  { refine !loop_EMadd1_succ @pv* _ @vp* !loop_EMadd1_succ,
  refine _ @h* !ap1_ptrunc_functor =>
  refine (@(ptrunc_pequiv_natural (n+1+1) _) _ _)^-1ʰ* @h* _,
  refine !to_pmap_freudenthal_pequiv @pv* _ @vp* !to_pmap_freudenthal_pequiv,
  apply ptrunc_functor_psquare =>
  exact !loop_susp_unit_natural }
Defined.

Definition apn_EMadd1_pequiv_EM1_natural {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
  psquare (loopn_EMadd1_pequiv_EM1 G n) (loopn_EMadd1_pequiv_EM1 H n)
  (EM1_functor φ) (Ω->[n] (EMadd1_functor φ n)).
Proof.
  induction n with n IH,
  { exact (reflexivity _) },
  { refine pwhisker_left _ !loopn_EMadd1_pequiv_EM1_succ @* _,
  refine _ @* pwhisker_right _ !loopn_EMadd1_pequiv_EM1_succ^-1*,
  refine _ @h* !loopn_succ_in_inv_natural,
  exact IH @h* (apn_psquare n !loop_EMadd1_natural) }
Defined.

Definition homotopy_group_functor_EMadd1_functor {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
  hsquare (ghomotopy_group_EMadd1' G n) (ghomotopy_group_EMadd1' H n)
  φ (forall ->g[n+1] (EMadd1_functor φ n)).
Proof.
  refine hwhisker_left _ (to_fun_isomorphism_trans _ _) @hty _ @hty
  hwhisker_right _ (to_fun_isomorphism_trans _ _)^-1ʰᵗʸ =>
  refine _ @htyh (homotopy_group_homomorphism_psquare 1 (apn_EMadd1_pequiv_EM1_natural φ n)),
  apply homotopy_group_functor_EM1_functor
Defined.

Definition homotopy_group_functor_EMadd1_functor' {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
  hsquare (ghomotopy_group_EMadd1' G n)^-1ᵍ (ghomotopy_group_EMadd1' H n)^-1ᵍ
  (forall ->g[n+1] (EMadd1_functor φ n)) φ.
Proof. apply hhinverse, exact (homotopy_group_functor_EMadd1_functor φ n) end

  section infgroup
  open infgroup
Definition EM1_pmap_natural {G H : Group} {X Y : pType} (f : X ->* Y) (eX : G ->∞g Ωg X)
  (eY : H ->∞g Ωg Y) [H2 : is_trunc 1 X] [is_trunc 1 Y] (φ : G ->g H)
  (p : hsquare eX eY φ (Ωg-> f)) : psquare (EM1_pmap eX) (EM1_pmap eY) (EM1_functor φ) f.
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x using EM.set_rec,
  { exact point_eq f },
  { apply eq_pathover,
  refine ap_compose f _ _ @ph _ @hp (ap_compose (EM1_pmap eY) _ _)^-1,
  refine ap02 _ !elim_pth @ph _ @hp ap02 _ !elim_pth^-1,
  refine _ @hp !elim_pth^-1, apply transpose, exact square_of_eq_bot (p g) }},
  { exact (concat_1p _)^-1 }
Defined.

Definition EM1_pequiv'_natural {G H : Group} {X Y : pType} (f : X ->* Y) (eX : G <~>∞g Ωg X)
  (eY : H <~>∞g Ωg Y) [H1 : is_conn 0 X] [H2 : is_trunc 1 X] [is_conn 0 Y] [is_trunc 1 Y]
  (φ : G ->g H) (p : hsquare eX eY φ (Ω-> f)) :
  psquare (EM1_pequiv' eX) (EM1_pequiv' eY) (EM1_functor φ) f.
  EM1_pmap_natural f eX eY φ p

Definition EM1_pequiv_natural {G H : Group} {X Y : pType} (f : X ->* Y) (eX : G <~>g forall ₁ X)
  (eY : H <~>g forall ₁ Y) [H1 : is_conn 0 X] [H2 : is_trunc 1 X] [is_conn 0 Y] [is_trunc 1 Y]
  (φ : G ->g H) (p : hsquare eX eY φ (forall ->g[1] f)) :
  psquare (EM1_pequiv eX) (EM1_pequiv eY) (EM1_functor φ) f.
  EM1_pequiv'_natural f _ _ φ
Proof.
  assert p' : ptrunc_functor 0 (Ω-> f) o* pequiv_of_isomorphism eX ==*
  pequiv_of_isomorphism eY o* pmap_of_homomorphism φ, exact phomotopy_of_homotopy p,
  exact p' @h* (ptrunc_pequiv_natural 0 (Ω-> f)),
Defined.

Definition EM1_pequiv_type_natural {X Y : pType} (f : X ->* Y)
  [H1 : is_conn 0 X] [H2 : is_trunc 1 X] [H3 : is_conn 0 Y] [H4 : is_trunc 1 Y] :
  psquare (EM1_pequiv_type X) (EM1_pequiv_type Y) (EM1_functor (forall ->g[1] f)) f.
Proof. refine EM1_pequiv_natural f _ _ _ _, exact homotopy.rfl end

Definition EM_up_natural {G H : AbGroup} (φ : G ->g H) {X Y : pType} (f : X ->* Y) {n : ℕ}
  (eX : G ->∞g Ωg[succ (succ n)] X) (eY : H ->∞g Ωg[succ (succ n)] Y)
  (p : hsquare eX eY φ (Ωg->[succ (succ n)] f))
  : hsquare (EM_up eX) (EM_up eY) φ (Ω->[succ n] (Ω-> f)).
  p @htyh hsquare_of_psquare (loopn_succ_in_natural (succ n) f)

Definition EMadd1_pmap_natural {G H : AbGroup} {X Y : pType} (f : X ->* Y) (n : ℕ)
  (eX : G ->∞g Ωg[succ n] X) (eY : H ->∞g Ωg[succ n] Y)
  [HX : is_trunc (n.+1) X] [HY : is_trunc (n.+1) Y]
  (φ : G ->g H) (p : hsquare eX eY φ (Ωg->[succ n] f)) :
  psquare (EMadd1_pmap n eX) (EMadd1_pmap n eY) (EMadd1_functor φ n) f.
Proof.
  revert X Y f eX eY HX HY p, induction n with n IH: intros,
  { apply EM1_pmap_natural, exact p },
  { do 2 rewrite [EMadd1_pmap_succ], refine _ @* pwhisker_left _ !EMadd1_functor_succ^-1* =>
  refine (ptrunc_elim_pcompose ((succ n).+1) _ _)^-1* @* _ @*
  (ptrunc_elim_ptrunc_functor ((succ n).+1) _ _)^-1* =>
  apply ptrunc_elim_phomotopy,
  refine _ @* !susp_elim_susp_functor^-1* =>
  refine _ @* susp_elim_phomotopy (IH _ _ _ _ _
  (@is_trunc_loop _ _ HX) _ (EM_up_natural φ f eX eY p)),
  apply susp_elim_natural }
Defined.

Definition EMadd1_pequiv'_natural {G H : AbGroup} {X Y : pType} (f : X ->* Y) (n : ℕ)
  (eX : G <~>∞g Ωg[succ n] X) (eY : H <~>∞g Ωg[succ n] Y)
  [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] [is_conn n Y] [is_trunc (n.+1) Y]
  (φ : G ->g H) (p : hsquare eX eY φ (Ωg->[succ n] f)) :
  psquare (EMadd1_pequiv' n eX) (EMadd1_pequiv' n eY) (EMadd1_functor φ n) f.
  EMadd1_pmap_natural f n eX eY φ p

Definition EMadd1_pequiv_natural_local_instance {X : pType} (n : ℕ) [H : is_trunc (n.+1) X] :
  is_set (Ω[succ n] X).
  @(is_set_loopn (succ n) X) H

  local attribute EMadd1_pequiv_natural_local_instance [instance]

Definition EMadd1_pequiv_natural {G H : AbGroup} {X Y : pType} (f : X ->* Y) (n : ℕ)
  (eX : G <~>g forall g[n+1] X) (eY : H <~>g forall g[n+1] Y)
  [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] [H3 : is_conn n Y]
  [H4 : is_trunc (n.+1) Y] (φ : G ->g H) (p : hsquare eX eY φ (forall ->g[n+1] f)) :
  psquare (EMadd1_pequiv n eX) (EMadd1_pequiv n eY) (EMadd1_functor φ n) f.
  EMadd1_pequiv'_natural f n
  _ --(inf_isomorphism_of_isomorphism eX @∞g gtrunc_isomorphism (Ω[succ n] X))
  _ --(inf_isomorphism_of_isomorphism eY @∞g gtrunc_isomorphism (Ω[succ n] Y))
  φ (p @htyh hsquare_of_psquare (ptrunc_pequiv_natural 0 (Ω->[succ n] f)))

Defined. infgroup

Definition EMadd1_pequiv_succ_natural {G H : AbGroup} {X Y : pType} (f : X ->* Y) (n : ℕ)
  (eX : G <~>g forall ag[n+2] X) (eY : H <~>g forall ag[n+2] Y) [is_conn (n.+1) X] [is_trunc (n.+2) X]
  [is_conn (n.+1) Y] [is_trunc (n.+2) Y] (φ : G ->g H) (p : hsquare eX eY φ (forall ->g[n+2] f)) :
  psquare (EMadd1_pequiv_succ n eX) (EMadd1_pequiv_succ n eY) (EMadd1_functor φ (n+1)) f.
  @(EMadd1_pequiv_natural f (succ n) eX eY) _ _ _ _ φ p

Definition EMadd1_pequiv_type_natural {X Y : pType} (f : X ->* Y) (n : ℕ)
  [H1 : is_conn (n+1) X] [H2 : is_trunc (n+1+1) X]
  [H3 : is_conn (n+1) Y] [H4 : is_trunc (n+1+1) Y] :
  psquare (EMadd1_pequiv_type X n) (EMadd1_pequiv_type Y n)
  (EMadd1_functor (forall ->g[n+2] f) (succ n)) f.
  EMadd1_pequiv_succ_natural f n !isomorphism.refl !isomorphism.refl (forall ->g[n+2] f)
  proof fun a => idp qed

Definition EMadd1_pmap_equiv (n : ℕ) (X Y : pType) [is_conn (n+1) X] [is_trunc (n+1+1) X]
  [H4 : is_trunc (n+1+1) Y] : (X ->* Y) <~> forall ag[n+2] X ->g forall ag[n+2] Y.
Proof.
  have H4' : is_trunc ((n+1).+1) Y, from H4,
  have is_set (Ωg[succ (n+1)] Y), from is_set_loopn (n+1+1) Y,
  fapply equiv.MK,
  { exact forall ->g[n+2] },
  { intro φ, refine (_ o* EMadd1_functor φ (n+1)) o* (EMadd1_pequiv_type X n)^-1ᵉ* =>
  exact EMadd1_pmap (n+1) (gtrunc_isomorphism (Ωg[succ (n+1)] Y)) },
  { intro φ, apply homomorphism_eq,
  refine homotopy_group_functor_pcompose (n+2) _ _ @hty _ => exact sorry },     { intro f, apply path_pforall, refine (phomotopy_pinv_right_of_phomotopy _)^-1*,
  exact sorry (*apply EMadd1_pequiv_type_natural*) }
Defined.

Definition EM1_functor_trivial_homomorphism (G H : Group) :
  EM1_functor (trivial_homomorphism G H) ==* pconst (EM1 G) (EM1 H).
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x using EM.set_rec,
  { reflexivity },
  { apply eq_pathover_constant_right, apply hdeg_square,
  refine !elim_pth @ _, apply resp_one }},
  { reflexivity }
Defined.

Definition EMadd1_functor_trivial_homomorphism (G H : AbGroup) (n : ℕ) :
  EMadd1_functor (trivial_homomorphism G H) n ==* pconst (EMadd1 G n) (EMadd1 H n).
Proof.
  induction n with n h,
  { exact EM1_functor_trivial_homomorphism G H } =>
  { refine !EMadd1_functor_succ @* ptrunc_functor_phomotopy (n+2) _ @* !ptrunc_functor_pconst =>
  refine susp_functor_phomotopy h @* !susp_functor_pconst }
Defined.

Definition EMadd1_pfunctor (G H : AbGroup) (n : ℕ) :
  (G ->gg H) ->* EMadd1 G n ->** EMadd1 H n.
  Build_pMap (fun φ => EMadd1_functor φ n) (path_pforall (EMadd1_functor_trivial_homomorphism G H n))

Definition loopn_EMadd1_add (G : AbGroup) (n m : ℕ) : Ω[n] (EMadd1 G (m + n)) <~>* EMadd1 G m.
Proof.
  induction n with n e,
  { reflexivity },
  { refine !loopn_succ_in @e* Ω<~>[n] (loop_EMadd1 G (m + n))^-1ᵉ* @e* e }
Defined.

Definition loopn_EMadd1_add_of_eq (G : AbGroup) {n m k : ℕ} (p : m + n = k) : Ω[n] (EMadd1 G k) <~>* EMadd1 G m.
  by induction p; exact loopn_EMadd1_add G n m

Definition EM1_phomotopy {G : Group} {X : pType} [is_trunc 1 X] {f g : EM1 G ->* X} (h : Ω-> f == Ω-> g) :
  f ==* g.
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x using EM.set_rec with a,
  { exact point_eq f @ (point_eq g)^-1 },
  { apply eq_pathover, apply move_top_of_right, apply move_bot_of_right,
  apply move_top_of_left', apply move_bot_of_left, apply hdeg_square, exact h (pth a) }},
  { apply inv_con_cancel_right }
Defined.

  (* properties about EM *)

Definition deloopable_EM [instance] (G : AbGroup) (n : ℕ) : deloopable (EM G n).
  deloopable.mk (EMadd1 G n) (loop_EM G n)

Definition gEM (G : AbGroup) (n : ℕ) : InfGroup.
  InfGroup_of_deloopable (EM G n)

Definition gloop_EM1 (G : Group) : Ωg (EM1 G) <~>∞g InfGroup_of_Group G.
  inf_isomorphism_of_equiv (EM.base_eq_base_equiv G) groupoid_quotient.encode_con

Definition gloop_EMadd1 (G : AbGroup) (n : ℕ) : Ωg (EMadd1 G n) <~>∞g gEM G n.
  deloop_isomorphism (EM G n)

Definition gEM0_isomorphism (G : AbGroup) : gEM G 0 <~>∞g InfGroup_of_Group G.
  (gloop_EMadd1 G 0)^-1ᵍ⁸ @∞g gloop_EM1 G

Definition gEM_functor {G H : AbGroup} (φ : G ->g H) (n : ℕ) : gEM G n ->∞g gEM H n.
  gloop_EMadd1 H n o∞g Ωg-> (EMadd1_functor φ n) o∞g (gloop_EMadd1 G n)^-1ᵍ⁸

Definition EM_pmap {G : AbGroup} (X : InfGroup) (n : ℕ)
  (e : AbInfGroup_of_AbGroup G ->∞g Ωg'[n] X) [H : is_trunc n X] : EM G n ->* X.
Proof.
  cases n with n,
  { exact pmap_of_inf_homomorphism e },
  { have is_trunc (n.+1) X, from H, exact EMadd1_pmap n e }
Defined.

Definition EM_homomorphism_gloop {G : AbGroup} (X : pType) (n : ℕ)
  (e : AbInfGroup_of_AbGroup G ->∞g Ωg[succ n] X) [H : is_trunc (n+1) X] : gEM G n ->∞g Ωg X.
  Ωg-> (EMadd1_pmap n e) o∞g !InfGroup_equiv_closed_isomorphism^-1ᵍ⁸

Definition gloopn_succ_in' (n : ℕ) (A : pType) : Ωg[succ n] A <~>∞g Ωg'[n] (Ωg A).
  inf_isomorphism_of_equiv (loopn_succ_in n A)
  (by cases n with n; apply is_mul_hom_id; exact loopn_succ_in_con)

Definition EM_homomorphism_deloopable {G : AbGroup} (X : pType) (H : deloopable X) (n : ℕ)
  (e : AbInfGroup_of_AbGroup G ->∞g Ωg'[n] (InfGroup_of_deloopable X)) (H : is_trunc (n+1) (deloop X)) :
  gEM G n ->∞g InfGroup_of_deloopable X.
  deloop_isomorphism X o∞g
  EM_homomorphism_gloop (deloop X) n
  ((gloopn_succ_in' n (deloop X))^-1ᵍ⁸ o∞g Ωg'->[n] (deloop_isomorphism X)^-1ᵍ⁸ o∞g e)


  (* an enriched homomorphism *)
Definition EM_ehomomorphism (G H : AbGroup) (n : ℕ) :
  InfGroup_of_Group (G ->gg H) ->∞g InfGroup_of_deloopable (EM G n ->** EM H n).
  inf_homomorphism.mk (fun φ => EM_functor φ n)
Proof.
  intro φ ψ,
  apply path_pforall,
  exact sorry
Defined.



  (* The Eilenberg-MacLane space K(G,n) with the same homotopy group as X on level n.
  On paper this is written K(forall ₙ(X), n). The problem is that for
  * n = 0 the expression forall ₀(X) is a pointed set, and K(X,0) needs X to be a pointed set
  * n = 1 the expression forall ₁(X) is a group, and K(G,1) needs G to be a group
  * n ≥ 2 the expression forall ₙ(X) is an abelian, and K(G,n) needs X to be an abelian group

  *)
Definition EM_type (X : pType) : ℕ -> pType
  | 0     . ptrunc 0 X
  | 1     . EM1 (forall ₁ X)
  | (n+2) . EMadd1 (forall ag[n+2] X) (n+1)

Definition EM_type_pequiv {X Y : pType.{u}} (n : ℕ) [Hn : is_succ n] (e : forall g[n] Y <~>g forall g[n] X)
  [H1 : is_conn (n.-1) X] [H2 : is_trunc n X] : EM_type Y n <~>* X.
Proof.
  induction Hn with n, cases n with n,
  { have is_conn 0 X, from H1,
  have is_trunc 1 X, from H2,
  exact EM1_pequiv e },
  { have is_conn (n+1) X, from H1,
  have is_trunc ((n+1).+1) X, from H2,
  exact EMadd1_pequiv (n+1) e }
Defined.








Defined.

  section category
  (* category *)
  structure ptruncconntype' (n : ℕ₋₂) : Type.
  (A : pType)
  (H1 : is_conn n A)
  (H2 : is_trunc (n+1) A)

  attribute ptruncconntype'.A [coercion]
  attribute ptruncconntype'.H1 ptruncconntype'.H2 [instance]

Definition ptruncconntype'_equiv_ptruncconntype (n : ℕ₋₂) :
  (ptruncconntype' n : Type.{u+1}) <~> ((n+1)-pType[n] : Type.{u+1}).
Proof.
  fapply equiv.MK,
  { intro X, exact ptruncconntype.mk (ptruncconntype'.A X) _ (point _) _ },
  { intro X, exact ptruncconntype'.mk X _ _ },
  { intro X, induction X with X H1 x₀ H2, reflexivity },
  { intro X, induction X with X H1 H2, induction X with X x₀, reflexivity }
Defined.

Definition EM1_pequiv_ptruncconntype' (X : ptruncconntype' 0) : EM1 (forall g[1] X) <~>* X.
  @(EM1_pequiv_type X) _ (ptruncconntype'.H2 X)

Definition EMadd1_pequiv_ptruncconntype' {n : ℕ} (X : ptruncconntype' (n+1)) :
  EMadd1 (forall ag[n+2] X) (succ n) <~>* X.
  @(EMadd1_pequiv_type X n) _ (ptruncconntype'.H2 X)

  open trunc_index
Definition is_set_pmap_ptruncconntype {n : ℕ₋₂} (X Y : ptruncconntype' n) : is_set (X ->* Y).
Proof.
  cases n with n, { exact _ },
  cases Y with Y H1 H2, cases Y with Y y₀,
  exact is_trunc_pmap_of_is_conn X n _ -1 _ (pointed.MK Y y₀) !le.refl H2,
Defined.

  open category functor nat_trans

Definition precategory_ptruncconntype' (n : ℕ₋₂) :
  precategory.{u+1 u} (ptruncconntype' n).
Proof.
  fapply precategory.mk,
  { exact fun X Y => X ->* Y },
  { exact is_set_pmap_ptruncconntype },
  { exact fun X Y Z g f => g o* f },
  { exact fun X => pid X },
  { intros, apply path_pforall, exact !passoc^-1* },
  { intros, apply path_pforall, apply pid_pcompose },
  { intros, apply path_pforall, apply pcompose_pid }
Defined.

Definition cptruncconntype' (n : ℕ₋₂) : Precategory.
  precategory.Mk (precategory_ptruncconntype' n)

  notation `cpType[`:95 n `]`:0 . cptruncconntype' n

Definition tEM1 (G : Group) : ptruncconntype' 0.
  ptruncconntype'.mk (EM1 G) _ !is_trunc_EM1

Definition tEM (G : AbGroup) (n : ℕ) : ptruncconntype' (n.-1).
  ptruncconntype'.mk (EM G n) _ !is_trunc_EM

Definition EM1_cfunctor : Grp ⇒ cpType[0].
  functor.mk
  (fun G => tEM1 G)
  (fun G H φ => EM1_functor φ)
Proof. intro, fapply path_pforall, apply EM1_functor_gid end
Proof. intros, fapply path_pforall, apply EM1_functor_gcompose end

Definition EM_cfunctor (n : ℕ) : AbGrp ⇒ cpType[n.-1].
  functor.mk
  (fun G => tEM G n)
  (fun G H φ => EM_functor φ n)
Proof. intro, fapply path_pforall, apply EM_functor_gid end
Proof. intros, fapply path_pforall, apply EM_functor_gcompose end

Definition homotopy_group_cfunctor : cpType[0] ⇒ Grp.
  functor.mk
  (fun X => forall g[1] X)
  (fun X Y (f : X ->* Y) => forall ->g[1] f)
Proof. intro, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_pid end
Proof. intros, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_pcompose end

Definition ab_homotopy_group_cfunctor (n : ℕ) : cpType[n.+1] ⇒ AbGrp.
  functor.mk
  (fun X => forall ag[n+2] X)
  (fun X Y (f : X ->* Y) => by rexact forall ->g[n+2] f)
Proof. intro, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_pid end
Proof. intros, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_pcompose end

Definition is_equivalence_EM1_cfunctor : is_equivalence EM1_cfunctor.{u}.
Proof.
  fapply is_equivalence.mk,
  { exact homotopy_group_cfunctor.{u} } =>
  { fapply natural_iso.mk,
  { fapply nat_trans.mk,
  { intro G, exact (fundamental_group_EM1' G)^-1ᵍ } =>
  { intro G H φ, apply homomorphism_eq, exact hhinverse (homotopy_group_functor_EM1_functor φ) }} =>
  { intro G, fapply iso.is_iso.mk,
  { exact fundamental_group_EM1' G } =>
  { apply homomorphism_eq,
  exact to_right_inv (equiv_of_isomorphism (fundamental_group_EM1' G)) => },
  { apply homomorphism_eq,
  exact to_left_inv (equiv_of_isomorphism (fundamental_group_EM1' G)) => }}},
  { fapply natural_iso.mk,
  { fapply nat_trans.mk,
  { intro X, exact EM1_pequiv_ptruncconntype' X },
  { intro X Y f, apply path_pforall, apply EM1_pequiv_type_natural }},
  { intro X, fapply iso.is_iso.mk,
  { exact (EM1_pequiv_ptruncconntype' X)^-1ᵉ* },
  { apply path_pforall, apply pleft_inv },
  { apply path_pforall, apply pright_inv }}}
Defined.

Definition is_equivalence_EM_cfunctor (n : ℕ) : is_equivalence (EM_cfunctor.{u} (n+2)).
Proof.
  fapply is_equivalence.mk,
  { exact ab_homotopy_group_cfunctor.{u} n } =>
  { fapply natural_iso.mk,
  { fapply nat_trans.mk,
  { intro G, exact (ghomotopy_group_EMadd1' G (n+1))^-1ᵍ },
  { intro G H φ, apply homomorphism_eq, exact homotopy_group_functor_EMadd1_functor' φ (n+1) }} =>
  { intro G, fapply iso.is_iso.mk,
  { exact ghomotopy_group_EMadd1' G (n+1) },
  { apply homomorphism_eq,
  exact to_right_inv (equiv_of_isomorphism (ghomotopy_group_EMadd1' G (n+1))), },
  { apply homomorphism_eq,
  exact to_left_inv (equiv_of_isomorphism (ghomotopy_group_EMadd1' G (n+1))), }}},
  { fapply natural_iso.mk,
  { fapply nat_trans.mk,
  { intro X, exact EMadd1_pequiv_ptruncconntype' X },
  { intro X Y f, apply path_pforall, apply EMadd1_pequiv_type_natural }},
  { intro X, fapply iso.is_iso.mk,
  { exact (EMadd1_pequiv_ptruncconntype' X)^-1ᵉ* },
  { apply path_pforall, apply pleft_inv },
  { apply path_pforall, apply pright_inv }}}
Defined.

Definition Grp_equivalence_cptruncconntype' : Grp.{u} <~>c cpType[0].
  equivalence.mk EM1_cfunctor.{u} is_equivalence_EM1_cfunctor.{u}

Definition AbGrp_equivalence_cptruncconntype' (n : ℕ) : AbGrp.{u} <~>c cpType[n.+1].
  equivalence.mk (EM_cfunctor.{u} (n+2)) (is_equivalence_EM_cfunctor.{u} n)
Defined. category

Definition pequiv_EMadd1_of_loopn_pequiv_EM1 {G : AbGroup} {X : pType} (n : ℕ)
  (e : Ω[n] X <~>* EM1 G) [H1 : is_conn n X] : X <~>* EMadd1 G n.
Proof.
  symmetry, apply EMadd1_pequiv, symmetry,
  refine isomorphism_of_eq (ap (fun x => forall g[x+1] X) !zero_add^-1) @g homotopy_group_add X 0 n @g _ @g
  !fundamental_group_EM1 =>
  exact homotopy_group_isomorphism_of_pequiv 0 e,
  refine is_trunc_of_is_trunc_loopn n 1 X _ (@is_conn_of_is_conn_succ _ _ H1),
  exact is_trunc_equiv_closed_rev 1 e _
Defined.

Definition EM1_pequiv_EM1 {G H : Group} (φ : G <~>g H) : EM1 G <~>* EM1 H.
  pequiv.MK (EM1_functor φ) (EM1_functor φ^-1ᵍ)
  abstract (EM1_functor_gcompose φ^-1ᵍ φ)^-1* @* EM1_functor_phomotopy proof left_inv φ qed @*
  EM1_functor_gid G end
  abstract (EM1_functor_gcompose φ φ^-1ᵍ)^-1* @* EM1_functor_phomotopy proof right_inv φ qed @*
  EM1_functor_gid H end

Definition is_contr_EM1 {G : Group} (H : is_contr G) : is_contr (EM1 G).
Proof.
  refine is_contr_of_is_conn_of_is_trunc _ !is_conn_EM1,
  refine is_trunc_succ_succ_of_is_trunc_loop _ _ _ _,
  refine is_trunc_equiv_closed _ !loop_EM1 _,
  apply is_trunc_succ, exact H
Defined.

Definition is_contr_EMadd1 (n : ℕ) {G : AbGroup} (H : is_contr G) : is_contr (EMadd1 G n).
Proof.
  induction n with n IH,
  { exact is_contr_EM1 H },
  { have is_contr (ptrunc (n+2) (susp (EMadd1 G n))), from _,
  exact this }
Defined.

Definition is_contr_EM (n : ℕ) {G : AbGroup} (H : is_contr G) : is_contr (K G n).
Proof.
  cases n with n,
  { exact H },
  { exact is_contr_EMadd1 n H }
Defined.

Definition EMadd1_pequiv_EMadd1 (n : ℕ) {G H : AbGroup} (φ : G <~>g H) : EMadd1 G n <~>* EMadd1 H n.
  pequiv.MK (EMadd1_functor φ n) (EMadd1_functor φ^-1ᵍ n)
  abstract (EMadd1_functor_gcompose φ^-1ᵍ φ n)^-1* @* EMadd1_functor_phomotopy proof left_inv φ qed n @*
  EMadd1_functor_gid G n end
  abstract (EMadd1_functor_gcompose φ φ^-1ᵍ n)^-1* @* EMadd1_functor_phomotopy proof right_inv φ qed n @*
  EMadd1_functor_gid H n end

Definition EM_pequiv_EM (n : ℕ) {G H : AbGroup} (φ : G <~>g H) : K G n <~>* K H n.
Proof.
  cases n with n,
  { exact pequiv_of_isomorphism φ },
  { exact EMadd1_pequiv_EMadd1 n φ }
Defined.

Definition ppi_EMadd1 {X : pType} (Y : X -> pType) (n : ℕ) :
  (ppforall (x : X), EMadd1 (forall ag[n+2] (Y x)) (n+1)) <~>* EMadd1 (forall ag[n+2] (ppforall (x : X), Y x)) (n+1).
Proof.
  exact sorry
Defined.
--EM_spectrum (forall , EM_spectrum (forall ₛ[s] (Y x))) k


  (* fiber of EM_functor *)
  open fiber
Definition is_trunc_fiber_EM1_functor {G H : Group} (φ : G ->g H) :
  is_trunc 1 (pfiber (EM1_functor φ)).
  is_trunc_pfiber _ _ _ _

Definition is_conn_fiber_EM1_functor {G H : Group} (φ : G ->g H) :
  is_conn -1 (pfiber (EM1_functor φ)).
Proof.
  apply is_conn_fiber_of_is_conn
Defined.

Definition is_trunc_fiber_EMadd1_functor {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
  is_trunc (n+1) (pfiber (EMadd1_functor φ n)).
  is_trunc_pfiber _ _ _ _

Definition is_conn_fiber_EMadd1_functor {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
  is_conn (n.-1) (pfiber (EMadd1_functor φ n)).
Proof.
  apply is_conn_fiber_of_is_conn, apply is_conn_of_is_conn_succ, apply is_conn_EMadd1,
  apply is_conn_EMadd1
Defined.

Definition is_trunc_fiber_EM_functor {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
  is_trunc n (pfiber (EM_functor φ n)).
  is_trunc_pfiber _ _ _ _

Definition is_conn_fiber_EM_functor {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
  is_conn (n.-2) (pfiber (EM_functor φ n)).
Proof.
  apply is_conn_fiber_of_is_conn, apply is_conn_of_is_conn_succ
Defined.

  section
  open chain_complex prod fin

  (* TODO: other cases *)
Definition LES_isomorphism_kernel_of_trivial
  {X Y : pType.{u}} (f : X ->* Y) (n : ℕ) [H : is_succ n]
  (H1 : is_contr (forall g[n+1] Y)) : forall g[n] (pfiber f) <~>g Kernel (forall ->g[n] f).
Proof.
  induction H with n,
  have H2 : is_exact (forall ->g[n+1] (ppoint f)) (forall ->g[n+1] f),
  from is_exact_of_is_exact_at (is_exact_LES_of_homotopy_groups f (n+1, 0)),
  have H3 : is_exact (forall ->g[n+1] (boundary_map f) og ghomotopy_group_succ_in n Y)
  (forall ->g[n+1] (ppoint f)),
  from is_exact_of_is_exact_at (is_exact_LES_of_homotopy_groups f (n+1, 1)),
  exact isomorphism_kernel_of_is_exact H3 H2 H1
Defined.

Defined.

  open group algebra is_trunc
Definition homotopy_group_fiber_EM1_functor {G H : Group.{u}} (φ : G ->g H) :
  forall ₁ (pfiber (EM1_functor φ)) <~>g Kernel φ.
  have H1 : is_trunc 1 (EM1 H), from sorry,
  have H2 : 1 <[ℕ] 1 + 1, from sorry,
  LES_isomorphism_kernel_of_trivial (EM1_functor φ) 1
  (@trivial_homotopy_group_of_is_trunc _ 1 2 H1 H2) @g
  sorry

Definition homotopy_group_fiber_EMadd1_functor {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
  forall g[n+1] (pfiber (EMadd1_functor φ n)) <~>g Kernel φ.
  sorry

  (* TODO: move*)
Definition cokernel {G H : AbGroup} (φ : G ->g H) : AbGroup.
  quotient_ab_group (image φ)

  (* todo: in algebra/quotient_group, do the first steps without assuming that N is normal,
  then this is qg for (image φ) in H *)
Definition image_cosets {G H : Group} (φ : G ->g H) : Set*.
  sorry

Definition homotopy_group_EMadd1_functor1 {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
  forall g[n+1] (pfiber (EMadd1_functor φ (n+1))) <~>g cokernel φ.
  sorry

Definition homotopy_group_EMadd1_functor2 {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
  forall g[n+1] (pfiber (EMadd1_functor φ n)) <~>g Kernel φ.
  sorry

Definition trunc_fiber_EM1_functor {G H : Group} (φ : G ->g H) :
  ptrunc 0 (pfiber (EM1_functor φ)) <~>* image_cosets φ.
  sorry

Defined. EM
