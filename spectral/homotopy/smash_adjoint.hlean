
(* the adjunction between the smash product and pointed maps *)
import .smash .susp ..pointed_pi ..pyoneda

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge is_trunc
     function unit sigma susp sphere

namespace smash

  variables {A A' B B' C C' X X' : pType}

  (* we start by defining the unit of the adjunction *)
Definition pinr {A : pType} (B : pType) (a : A) : B ->* A ∧ B.
Proof.
    fapply Build_pMap,
    { intro b, exact smash.mk a b },
    { exact gluel' a (point _) }
Defined.

Definition pinr_phomotopy {a a' : A} (p : a = a') : pinr B a ==* pinr B a'.
Proof.
    fapply Build_pHomotopy,
    { exact ap010 (pmap.to_fun o pinr B) p } =>
    { induction p, apply idp_con }
Defined.

Definition smash_pmap_unit_pt (A B : pType)
    : pinr B (point _) ==* pconst B (A ∧ B).
Proof.
    fapply Build_pHomotopy,
    { intro b, exact gluer' b (point _) },
    { rexact con.right_inv (gluer (point _)) @ (con.right_inv (gluel (point _)))^-1 }
Defined.

Definition smash_pmap_unit (A B : pType) : A ->* ppMap B (A ∧ B).
Proof.
    fapply Build_pMap,
    { exact pinr B },
    { apply path_pforall, exact smash_pmap_unit_pt A B }
Defined.

  (* The unit is natural in the first argument *)
Definition smash_functor_pid_pinr' (B : pType) (f : A ->* A') (a : A) :
    pinr B (f a) ==* smash_functor f (pid B) o* pinr B a.
Proof.
    fapply Build_pHomotopy,
    { intro b, reflexivity },
    { refine (concat_1p _) @ _,
      induction A' with A' a₀', induction f with f f₀, esimp at *,
      induction f₀, rexact functor_gluel'2 f (@id B) a (point _) }
Defined.

Definition smash_pmap_unit_pt_natural (B : pType) (f : A ->* A') :
    smash_functor_pid_pinr' B f (point _) @*
    pwhisker_left (smash_functor f (pid B)) (smash_pmap_unit_pt A B) @*
    pcompose_pconst (f ∧-> (pid B)) =
    pinr_phomotopy (point_eq f) @* smash_pmap_unit_pt A' B.
Proof.
    induction f with f f₀, induction A' with A' a₀', esimp at *,
    induction f₀, refine _ @ !refl_trans^-1,
    refine !trans_refl @ _,
    fapply phomotopy_eq',
    { intro b, refine (concat_1p _) @ _,
      rexact functor_gluer'2 f (pid B) b (point _) } =>
    { refine whisker_right_idp _ @ph _,
      refine ap (fun x => _ @ x) _ @ph _,
      rotate 1, rexact (functor_gluer'2_same f (pid B) (point _)) =>
      refine whisker_right _ (concat_1p _) @pv _,
      refine (concat_pp_p _ _ _)^-1 @ph _, apply whisker_bl,
      refine whisker_left _ !point_htpy_mk @pv _,
      refine (concat_pp_p _ _ _)^-1 @ whisker_right _ _ @pv _,
      rotate 1, esimp, apply whisker_left_idp_con,
      refine (concat_pp_p _ _ _) @pv _, apply whisker_tl,
      refine whisker_right _ (concat_1p _) @pv _,
      refine whisker_right _ !whisker_right_idp @pv _,
      refine whisker_right _ ((concat_1p _) @ !ap02_con) @ (concat_pp_p _ _ _) @pv _,
      apply whisker_tl,
      apply vdeg_square,
      refine whisker_right _ !ap_inv @ _, apply inv_con_eq_of_eq_con,
      rexact functor_gluel'2_same (pmap_of_map f (point _)) (pmap_of_map id (Point B)) (point _) }
Defined.

Definition smash_pmap_unit_natural (B : pType) (f : A ->* A') :
    psquare (smash_pmap_unit A B) (smash_pmap_unit A' B) f (ppcompose_left (f ∧-> pid B)).
Proof.
    apply ptranspose,
    induction A with A a₀, induction B with B b₀, induction A' with A' a₀',
    induction f with f f₀, esimp at *, induction f₀, fapply phomotopy_mk_ppMap,
    { intro a, exact smash_functor_pid_pinr' _ (pmap_of_map f a₀) a } =>
    { refine ap (fun x => _ @* phomotopy_path x) !point_eq_pcompose @ _
           @ ap phomotopy_path !point_eq_pcompose^-1,
      esimp, refine _ @ ap phomotopy_path (concat_1p _)^-1,
      refine _ @ !phomotopy_path_of_phomotopy^-1,
      refine ap (fun x => _ @* phomotopy_path (x @ _)) !pcompose_left_path_pforall @ _,
      refine ap (fun x => _ @* x) (!phomotopy_path_con @
               !phomotopy_path_of_phomotopy ◾** !phomotopy_path_of_phomotopy @ !trans_refl) @ _,
      refine _ @ smash_pmap_unit_pt_natural _ (pmap_of_map f a₀) @ _,
      { exact !trans_refl^-1 },
      { exact !refl_trans }}
Defined.

  (* The unit is also dinatural in the first argument, but that's easier to prove after the adjunction.
     We don't need it for the adjunction *)

  (* The counit *)
Definition smash_pmap_counit_map (fb : ppMap B C ∧ B) : C.
Proof.
    induction fb with f b f b,
    { exact f b },
    { exact (point _) },
    { exact (point _) },
    { exact point_eq f },
    { reflexivity }
Defined.

Definition smash_pmap_counit (B C : pType) : ppMap B C ∧ B ->* C.
Proof.
    fapply Build_pMap,
    { exact smash_pmap_counit_map },
    { reflexivity }
Defined.

  (* The counit is natural in both arguments *)
Definition smash_pmap_counit_natural_right (B : pType) (g : C ->* C') :
    psquare (smash_pmap_counit B C) (smash_pmap_counit B C') (ppcompose_left g ∧-> pid B) g.
Proof.
    apply ptranspose,
    fapply Build_pHomotopy,
    { intro fb, induction fb with f b f b,
      { reflexivity },
      { exact (point_eq g)^-1 },
      { exact (point_eq g)^-1 },
      { apply eq_pathover,
        refine ap_compose (smash_pmap_counit B C') _ _ @ph _ @hp (ap_compose g _ _)^-1,
        refine ap02 _ !functor_gluel @ph _ @hp ap02 _ !elim_gluel^-1 =>
        refine (ap_pp _ _ _) @ !ap_compose' ◾ !elim_gluel @ph _,
        refine (concat_1p _) @ph _, apply square_of_eq,
        refine (concat_1p _) @ !con_inv_cancel_right^-1 },
      { apply eq_pathover,
        refine ap_compose (smash_pmap_counit B C') _ _ @ph _ @hp (ap_compose g _ _)^-1,
        refine ap02 _ !functor_gluer @ph _ @hp ap02 _ !elim_gluer^-1 =>
        refine (ap_pp _ _ _) @ !ap_compose' ◾ !elim_gluer @ph _^-1ʰ,
        apply square_of_eq_bot, refine (concat_1p _) @ _,
        induction C' with C' c₀', induction g with g g₀, esimp at *,
        induction g₀, refine ap02 _ !path_pforall_refl }},
    { refine (concat_1p _) @ (concat_1p _) @ _, refine _ @ !ap_compose,
      refine _ @ (ap_is_constant point_eq _)^-1, refine (concat_1p _)^-1 }
Defined.

Definition smash_pmap_counit_natural_left (C : pType) (g : B ->* B') :
    psquare (pid (ppMap B' C) ∧-> g) (smash_pmap_counit B C)
            (ppcompose_right g ∧-> pid B) (smash_pmap_counit B' C).
Proof.
    fapply Build_pHomotopy,
    { intro af, induction af with a f a f,
      { reflexivity },
      { reflexivity },
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        refine ap_compose !smash_pmap_counit _ _ @ ap02 _ !elim_gluel @ (ap_pp _ _ _) @
          !ap_compose' ◾ !elim_gluel @ _,
        refine (ap_compose !smash_pmap_counit _ _ @ ap02 _ !elim_gluel @ (ap_pp _ _ _) @
          !ap_compose' ◾ !elim_gluel @ (concat_1p _))^-1 },
      { apply eq_pathover, apply hdeg_square,
        refine ap_compose !smash_pmap_counit _ _ @ ap02 _ (!elim_gluer @ (concat_1p _)) @
          !elim_gluer @ _,
        refine (ap_compose !smash_pmap_counit _ _ @ ap02 _ !elim_gluer @ (ap_pp _ _ _) @
          !ap_compose' ◾ !elim_gluer @ (concat_p1 _) @ _)^-1,
        refine !to_fun_path_pforall , reflexivity }},
    { refine (concat_1p _) @ _, refine !ap_compose' @ _ @ !ap_ap011^-1, esimp,
      refine !to_fun_path_pforall , exact (ap_pp _ _ _)stant^-1 }
Defined.

  (* The unit-counit laws *)
Definition smash_pmap_unit_counit (A B : pType) :
    smash_pmap_counit B (A ∧ B) o* smash_pmap_unit A B ∧-> pid B ==* pid (A ∧ B).
Proof.
    fapply Build_pHomotopy,
    { intro x,
      induction x with a b a b,
      { reflexivity },
      { exact gluel (point _) },
      { exact gluer (point _) },
      { apply eq_pathover_id_right,
        refine ap_compose smash_pmap_counit_map _ _ @ ap02 _ !functor_gluel @ph _ =>
        refine (ap_pp _ _ _) @ !ap_compose' ◾ !elim_gluel @ph _,
        refine (concat_1p _) @ph _,
        apply square_of_eq, refine (concat_1p _) @ !inv_con_cancel_right^-1 },
      { apply eq_pathover_id_right,
        refine ap_compose smash_pmap_counit_map _ _ @ ap02 _ !functor_gluer @ph _ =>
        refine (ap_pp _ _ _) @ !ap_compose' ◾ !elim_gluer @ph _,
        refine !ap_path_pforall @ph _,
        apply square_of_eq, refine (concat_1p _) @ !inv_con_cancel_right^-1 }},
    { refine _ @ !ap_compose, refine _ @ (ap_is_constant point_eq _)^-1,
         rexact (con.right_inv (gluel (point _)))^-1 }
Defined.

Definition smash_pmap_counit_unit_pt (f : A ->* B) :
    smash_pmap_counit A B o* pinr A f ==* f.
Proof.
    fapply Build_pHomotopy,
    { intro a, reflexivity },
    { refine (concat_1p _) @ !elim_gluel'^-1 }
Defined.

Definition smash_pmap_counit_unit (A B : pType) :
    ppcompose_left (smash_pmap_counit A B) o* smash_pmap_unit (ppMap A B) A ==* pid (ppMap A B).
Proof.
    fapply phomotopy_mk_ppMap,
    { intro f, exact smash_pmap_counit_unit_pt f },
    { refine !trans_refl @ _,
      refine _ @ ap (fun x => phomotopy_path (x @ _)) !pcompose_left_path_pforall^-1,
      refine _ @ !phomotopy_path_con^-1,
      refine _ @ !phomotopy_path_of_phomotopy^-1 ◾** !phomotopy_path_of_phomotopy^-1,
      refine _ @ !trans_refl^-1,
      fapply phomotopy_eq,
      { intro a, esimp, refine !elim_gluer'^-1 },
      { esimp, refine whisker_right _ !whisker_right_idp @ _ @ (concat_1p _)^-1,
        refine whisker_right _ !elim_gluer'_same⁻² @ _ @ !elim_gluel'_same^-1⁻²,
        apply inv_con_eq_of_eq_con, refine (concat_1p _) @ _, esimp,
        refine _ @ !ap02_con @ whisker_left _ !ap_inv,
        refine !whisker_right_idp @ _,
        exact (concat_1p _) }}
Defined.

  (* The underlying (unpointed) functions of the equivalence A ->* (B ->* C) <~>* A ∧ B ->* C) *)
Definition smash_elim (f : A ->* ppMap B C) : A ∧ B ->* C.
  smash_pmap_counit B C o* f ∧-> pid B

Definition smash_elim_inv (g : A ∧ B ->* C) : A ->* ppMap B C.
  ppcompose_left g o* smash_pmap_unit A B

  (* They are inverses, constant on the constant function and natural *)
Definition smash_elim_left_inv (f : A ->* ppMap B C) : smash_elim_inv (smash_elim f) ==* f.
Proof.
    refine !pwhisker_right !ppcompose_left_pcompose @* _,
    refine !passoc @* _,
    refine !pwhisker_left !smash_pmap_unit_natural @* _,
    refine !passoc^-1* @* _,
    refine !pwhisker_right !smash_pmap_counit_unit @* _,
    apply pid_pcompose
Defined.

Definition smash_elim_right_inv (g : A ∧ B ->* C) : smash_elim (smash_elim_inv g) ==* g.
Proof.
    refine !pwhisker_left !smash_functor_pcompose_pid @* _ =>
    refine !passoc^-1* @* _,
    refine !pwhisker_right !smash_pmap_counit_natural_right^-1* @* _,
    refine !passoc @* _,
    refine !pwhisker_left !smash_pmap_unit_counit @* _,
    apply pcompose_pid
Defined.

Definition smash_elim_pconst (A B C : pType) :
    smash_elim (pconst A (ppMap B C)) ==* pconst (A ∧ B) C.
Proof.
    refine pwhisker_left _ (smash_functor_pconst_left (pid B)) @* !pcompose_pconst
Defined.

Definition smash_elim_inv_pconst (A B C : pType) :
    smash_elim_inv (pconst (A ∧ B) C) ==* pconst A (ppMap B C).
Proof.
    fapply phomotopy_mk_ppMap,
    { intro f, apply pconst_pcompose },
    { esimp, refine !trans_refl @ _,
      refine _ @ (!phomotopy_path_con @ (ap phomotopy_path !pcompose_left_path_pforall @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy)^-1,
      apply pconst_pcompose_phomotopy_pconst }
Defined.

Definition smash_elim_natural_right (f : C ->* C') (g : A ->* ppMap B C) :
    f o* smash_elim g ==* smash_elim (ppcompose_left f o* g).
Proof.
    refine _ @* pwhisker_left _ !smash_functor_pcompose_pid^-1* =>
    refine !passoc^-1* @* pwhisker_right _ _ @* !passoc,
    apply smash_pmap_counit_natural_right
Defined.

Definition smash_elim_inv_natural_right {A B C C' : pType} (f : C ->* C')
    (g : A ∧ B ->* C) : ppcompose_left f o* smash_elim_inv g ==* smash_elim_inv (f o* g).
Proof.
    refine !passoc^-1* @* pwhisker_right _ _,
    exact !ppcompose_left_pcompose^-1*
Defined.

Definition smash_elim_natural_left (f : A ->* A') (g : B ->* B') (h : A' ->* ppMap B' C) :
    smash_elim h o* (f ∧-> g) ==* smash_elim (ppcompose_right g o* h o* f).
Proof.
    refine !smash_functor_pcompose_pid @ph* _ =>
    refine _ @v* !smash_pmap_counit_natural_left,
    refine smash_functor_psquare !pid_pcompose^-1* (phrefl g)
Defined.

Definition smash_elim_phomotopy {f f' : A ->* ppMap B C} (p : f ==* f') :
    smash_elim f ==* smash_elim f'.
Proof.
    apply pwhisker_left,
    exact smash_functor_phomotopy p (reflexivity _)
Defined.

Definition smash_elim_inv_phomotopy {f f' : A ∧ B ->* C} (p : f ==* f') :
    smash_elim_inv f ==* smash_elim_inv f'.
  pwhisker_right _ (ppcompose_left_phomotopy p)

Definition smash_elim_path_pforall {f f' : A ->* ppMap B C} (p : f ==* f') :
    ap smash_elim (path_pforall p) = path_pforall (smash_elim_phomotopy p).
Proof.
    induction p using phomotopy_rec_idp,
    refine ap02 _ !path_pforall_refl @ _,
    refine !path_pforall_refl^-1 @ _,
    apply ap path_pforall,
    refine _ @ ap (pwhisker_left _) !smash_functor_phomotopy_refl^-1 =>
    refine !pwhisker_left_refl^-1
Defined.

Definition smash_elim_inv_path_pforall {f f' : A ∧ B ->* C} (p : f ==* f') :
    ap smash_elim_inv (path_pforall p) = path_pforall (smash_elim_inv_phomotopy p).
Proof.
    induction p using phomotopy_rec_idp,
    refine ap02 _ !path_pforall_refl @ _,
    refine !path_pforall_refl^-1 @ _,
    apply ap path_pforall,
    refine _ @ ap (pwhisker_right _) !ppcompose_left_phomotopy_refl^-1,
    refine !pwhisker_right_refl^-1
Defined.

  (* The pointed maps of the equivalence A ->* (B ->* C) <~>* A ∧ B ->* C *)
Definition smash_pelim (A B C : pType) : ppMap A (ppMap B C) ->* ppMap (A ∧ B) C.
  ppcompose_left (smash_pmap_counit B C) o* smash_functor_left A (ppMap B C) B

Definition smash_pelim_inv (A B C : pType) :
    ppMap (A ∧ B) C ->* ppMap A (ppMap B C).
  Build_pMap smash_elim_inv (path_pforall !smash_elim_inv_pconst)

  (* The forward function is natural in all three arguments *)
Definition smash_pelim_natural_left (B C : pType) (f : A' ->* A) :
    psquare (smash_pelim A B C) (smash_pelim A' B C)
            (ppcompose_right f) (ppcompose_right (f ∧-> pid B)).
  smash_functor_left_natural_left (ppMap B C) B f @h* !ppcompose_left_ppcompose_right

Definition smash_pelim_natural_middle (A C : pType) (f : B' ->* B) :
    psquare (smash_pelim A B C) (smash_pelim A B' C)
            (ppcompose_left (ppcompose_right f)) (ppcompose_right (pid A ∧-> f)).
  pwhisker_tl _ !ppcompose_left_ppcompose_right @*
  (!smash_functor_left_natural_right^-1* @pv*
  smash_functor_left_natural_middle _ _ (ppcompose_right f) @h*
  ppcompose_left_psquare !smash_pmap_counit_natural_left)

Definition smash_pelim_natural_right (A B : pType) (f : C ->* C') :
    psquare (smash_pelim A B C) (smash_pelim A B C')
            (ppcompose_left (ppcompose_left f)) (ppcompose_left f).
  smash_functor_left_natural_middle _ _ (ppcompose_left f) @h*
  ppcompose_left_psquare (smash_pmap_counit_natural_right _ f)

Definition smash_pelim_natural_lm (C : pType) (f : A' ->* A) (g : B' ->* B) :
    psquare (smash_pelim A B C) (smash_pelim A' B' C)
            (ppcompose_left (ppcompose_right g) o* ppcompose_right f) (ppcompose_right (f ∧-> g)).
  smash_pelim_natural_left B C f @v* smash_pelim_natural_middle A' C g @hp*
  ppcompose_right_phomotopy (smash_functor_split f g) @* !ppcompose_right_pcompose

Definition smash_pelim_pid (B C : pType) :
    smash_pelim (ppMap B C) B C !pid ==* smash_pmap_counit B C.
  pwhisker_left _ !smash_functor_pid @* !pcompose_pid

Definition smash_pelim_inv_pid (A B : pType) :
    smash_pelim_inv A B (A ∧ B) !pid ==* smash_pmap_unit A B.
  pwhisker_right _ !ppcompose_left_pid @* !pid_pcompose

  (* The equivalence (note: the forward function of smash_adjoint_pmap is smash_pelim_inv) *)
Definition is_equiv_smash_elim (A B C : pType) : is_equiv (@smash_elim A B C).
Proof.
    fapply adjointify,
    { exact smash_elim_inv },
    { intro g, apply path_pforall, exact smash_elim_right_inv g },
    { intro f, apply path_pforall, exact smash_elim_left_inv f }
Defined.

Definition smash_adjoint_pmap_inv (A B C : pType) :
    ppMap A (ppMap B C) <~>* ppMap (A ∧ B) C.
  pequiv_of_pmap (smash_pelim A B C) (is_equiv_smash_elim A B C)

Definition smash_adjoint_pmap (A B C : pType) :
    ppMap (A ∧ B) C <~>* ppMap A (ppMap B C).
  (smash_adjoint_pmap_inv A B C)^-1ᵉ*

  (* The naturality of the equivalence is a direct consequence of the earlier naturalities *)
Definition smash_adjoint_pmap_natural_right_pt {A B C C' : pType} (f : C ->* C') (g : A ∧ B ->* C) :
    ppcompose_left f o* smash_adjoint_pmap A B C g ==* smash_adjoint_pmap A B C' (f o* g).
  smash_elim_inv_natural_right f g

Definition smash_adjoint_pmap_inv_natural_right_pt {A B C C' : pType} (f : C ->* C')
    (g : A ->* ppMap B C) : f o* (smash_adjoint_pmap A B C)^-1ᵉ* g ==*
    (smash_adjoint_pmap A B C')^-1ᵉ* (ppcompose_left f o* g).
  smash_elim_natural_right f g

Definition smash_adjoint_pmap_inv_natural_right (A B : pType) (f : C ->* C') :
    psquare (smash_adjoint_pmap_inv A B C) (smash_adjoint_pmap_inv A B C')
            (ppcompose_left (ppcompose_left f)) (ppcompose_left f).
  smash_pelim_natural_right A B f

Definition smash_adjoint_pmap_natural_right (A B : pType) (f : C ->* C') :
    psquare (smash_adjoint_pmap A B C) (smash_adjoint_pmap A B C')
            (ppcompose_left f) (ppcompose_left (ppcompose_left f)).
  (smash_adjoint_pmap_inv_natural_right A B f)^-1ʰ*

Definition smash_adjoint_pmap_natural_lm (C : pType) (f : A ->* A') (g : B ->* B') :
    psquare (smash_adjoint_pmap A' B' C) (smash_adjoint_pmap A B C)
            (ppcompose_right (f ∧-> g)) (ppcompose_left (ppcompose_right g) o* ppcompose_right f).
  (smash_pelim_natural_lm C f g)^-1ʰ*

  (* some naturalities we skipped, but are now easier to prove *)
Definition smash_elim_inv_natural_middle (f : B' ->* B)
    (g : A ∧ B ->* C) : ppcompose_right f o* smash_elim_inv g ==* smash_elim_inv (g o* pid A ∧-> f).
  !pcompose_pid^-1* @* !passoc @* phomotopy_path (smash_adjoint_pmap_natural_lm C (pid A) f g)

Definition smash_pmap_unit_natural_left (f : B ->* B') :
    psquare (smash_pmap_unit A B) (ppcompose_right f)
            (smash_pmap_unit A B') (ppcompose_left (pid A ∧-> f)).
Proof.
    refine pwhisker_left _ !smash_pelim_inv_pid^-1* @* _ @* pwhisker_left _ !smash_pelim_inv_pid,
    refine !smash_elim_inv_natural_right @* _ @* !smash_elim_inv_natural_middle^-1*,
    refine pap smash_elim_inv (!pcompose_pid @* !pid_pcompose^-1*),
Defined.

  (* Corollary: associativity of smash *)

Definition smash_assoc_elim_pequiv (A B C X : pType) :
    ppMap (A ∧ (B ∧ C)) X <~>* ppMap ((A ∧ B) ∧ C) X.
  calc
    ppMap (A ∧ (B ∧ C)) X
        <~>* ppMap A (ppMap (B ∧ C) X)     : smash_adjoint_pmap A (B ∧ C) X
    ... <~>* ppMap A (ppMap B (ppMap C X)) : ppMap_pequiv_ppMap_right (smash_adjoint_pmap B C X)
    ... <~>* ppMap (A ∧ B) (ppMap C X)     : smash_adjoint_pmap_inv A B (ppMap C X)
    ... <~>* ppMap ((A ∧ B) ∧ C) X         : smash_adjoint_pmap_inv (A ∧ B) C X


Definition smash_assoc_elim_natural_left (X : pType)
    (f : A' ->* A) (g : B' ->* B) (h : C' ->* C) :
    psquare (smash_assoc_elim_pequiv A B C X) (smash_assoc_elim_pequiv A' B' C' X)
            (ppcompose_right (f ∧-> g ∧-> h)) (ppcompose_right ((f ∧-> g) ∧-> h)).
Proof.
    refine !smash_adjoint_pmap_natural_lm @h*
    (!ppcompose_left_ppcompose_right @v* ppcompose_left_psquare !smash_adjoint_pmap_natural_lm) @h*
    _ @h* !smash_pelim_natural_lm,
    refine pwhisker_right _ (ppcompose_left_phomotopy !ppcompose_left_ppcompose_right^-1* @*
      !ppcompose_left_pcompose) @* !passoc @* pwhisker_left _ !ppcompose_left_ppcompose_right^-1* @*
      !passoc^-1* @ph* _,
    refine _ @hp* !ppcompose_left_ppcompose_right^-1*,
    refine !smash_pelim_natural_right @v* !smash_pelim_natural_lm
Defined.

Definition smash_assoc_elim_natural_right (A B C : pType) (f : X ->* X') :
    psquare (smash_assoc_elim_pequiv A B C X) (smash_assoc_elim_pequiv A B C X')
            (ppcompose_left f) (ppcompose_left f).
  !smash_adjoint_pmap_natural_right @h*
  ppcompose_left_psquare !smash_adjoint_pmap_natural_right @h*
  !smash_adjoint_pmap_inv_natural_right @h*
  !smash_adjoint_pmap_inv_natural_right

Definition smash_assoc_elim_natural_right_pt (f : X ->* X') (g : A ∧ (B ∧ C) ->* X) :
    f o* smash_assoc_elim_pequiv A B C X g ==* smash_assoc_elim_pequiv A B C X' (f o* g).
Proof.
    refine !smash_adjoint_pmap_inv_natural_right_pt @* _,
    apply smash_elim_phomotopy,
    refine !smash_adjoint_pmap_inv_natural_right_pt @* _,
    apply smash_elim_phomotopy,
    refine !passoc^-1* @* _,
    refine pwhisker_right _ !smash_adjoint_pmap_natural_right @* _,
    refine !passoc @* _,
    apply pwhisker_left,
    refine !smash_adjoint_pmap_natural_right_pt
Defined.

Definition smash_assoc_elim_inv_natural_right_pt (f : X ->* X') (g : (A ∧ B) ∧ C ->* X) :
    f o* (smash_assoc_elim_pequiv A B C X)^-1ᵉ* g ==*
    (smash_assoc_elim_pequiv A B C X')^-1ᵉ* (f o* g).
  phomotopy_path ((smash_assoc_elim_natural_right A B C f)^-1ʰ* g)

Definition smash_assoc (A B C : pType) : (A ∧ B) ∧ C <~>* A ∧ (B ∧ C).
  pyoneda (smash_assoc_elim_pequiv A B C) (fun X X' f => smash_assoc_elim_natural_right A B C f)

Definition pcompose_smash_assoc {A B C X : pType} (f : A ∧ (B ∧ C) ->* X) :
    f o* smash_assoc A B C ==* smash_assoc_elim_pequiv A B C X f.
  smash_assoc_elim_natural_right_pt f !pid @* pap !smash_assoc_elim_pequiv !pcompose_pid

Definition pcompose_smash_assoc_pinv {A B C X : pType} (f : (A ∧ B) ∧ C ->* X) :
    f o* (smash_assoc A B C)^-1ᵉ* ==* (smash_assoc_elim_pequiv A B C X)^-1ᵉ* f.
  smash_assoc_elim_inv_natural_right_pt f !pid @* pap !smash_assoc_elim_pequiv^-1ᵉ* !pcompose_pid

  (* the associativity of smash is natural in all arguments *)
Definition smash_assoc_natural (f : A ->* A') (g : B ->* B') (h : C ->* C') :
    psquare (smash_assoc A B C) (smash_assoc A' B' C') ((f ∧-> g) ∧-> h) (f ∧-> (g ∧-> h)).
Proof.
    refine !pcompose_smash_assoc @* _,
    refine pap !smash_assoc_elim_pequiv !pid_pcompose^-1* @* _,
    rexact phomotopy_path (smash_assoc_elim_natural_left _ f g h !pid)^-1
Defined.

  (* we prove the pentagon for the associativity *)
Definition smash_assoc_elim_left_pequiv (A B C D X : pType) :
    ppMap (D ∧ (A ∧ (B ∧ C))) X <~>* ppMap (D ∧ ((A ∧ B) ∧ C)) X.
  calc     ppMap (D ∧ (A ∧ (B ∧ C))) X
        <~>* ppMap D (ppMap (A ∧ (B ∧ C)) X) : smash_adjoint_pmap D (A ∧ (B ∧ C)) X
    ... <~>* ppMap D (ppMap ((A ∧ B) ∧ C) X) : ppMap_pequiv_ppMap_right (smash_assoc_elim_pequiv A B C X)
    ... <~>* ppMap (D ∧ ((A ∧ B) ∧ C)) X     : smash_adjoint_pmap_inv D ((A ∧ B) ∧ C) X

Definition smash_assoc_elim_right_pequiv (A B C D X : pType) :
    ppMap ((A ∧ (B ∧ C)) ∧ D) X <~>* ppMap (((A ∧ B) ∧ C) ∧ D) X.
  calc     ppMap ((A ∧ (B ∧ C)) ∧ D) X
        <~>* ppMap (A ∧ (B ∧ C)) (ppMap D X) : smash_adjoint_pmap (A ∧ (B ∧ C)) D X
    ... <~>* ppMap ((A ∧ B) ∧ C) (ppMap D X) : smash_assoc_elim_pequiv A B C (ppMap D X)
    ... <~>* ppMap (((A ∧ B) ∧ C) ∧ D) X     : smash_adjoint_pmap_inv ((A ∧ B) ∧ C) D X

Definition smash_assoc_elim_right_natural_right (A B C D : pType) (f : X ->* X') :
    psquare (smash_assoc_elim_right_pequiv A B C D X) (smash_assoc_elim_right_pequiv A B C D X')
            (ppcompose_left f) (ppcompose_left f).
  smash_adjoint_pmap_natural_right (A ∧ (B ∧ C)) D f @h*
  smash_assoc_elim_natural_right A B C (ppcompose_left f) @h*
  smash_adjoint_pmap_inv_natural_right ((A ∧ B) ∧ C) D f

Definition smash_assoc_smash_functor (A B C D : pType) :
    smash_assoc A B C ∧-> pid D ==* !smash_assoc_elim_right_pequiv (pid _).
Proof.
    symmetry,
    refine pap (!smash_adjoint_pmap_inv o* !smash_assoc_elim_pequiv) !smash_pelim_inv_pid @* _,
    refine pap !smash_adjoint_pmap_inv !pcompose_smash_assoc^-1* @* _,
    refine pwhisker_left _ !smash_functor_pcompose_pid @* _ =>
    refine !passoc^-1* @* _,
    exact pwhisker_right _ !smash_pmap_unit_counit @* !pid_pcompose,
Defined.

Definition ppcompose_right_smash_assoc (A B C X : pType) :
    ppcompose_right (smash_assoc A B C) ==* smash_assoc_elim_pequiv A B C X.
  sorry

Definition smash_functor_smash_assoc (A B C D : pType) :
    pid A ∧-> smash_assoc B C D ==* !smash_assoc_elim_left_pequiv (pid _).
Proof.
    symmetry,
    refine pap (!smash_adjoint_pmap_inv o* ppcompose_left _) !smash_pelim_inv_pid @* _,
    refine pap !smash_adjoint_pmap_inv (pwhisker_right _ !ppcompose_right_smash_assoc^-1* @*
      !smash_pmap_unit_natural_left^-1*) @* _,
    refine phomotopy_path (smash_adjoint_pmap_inv_natural_right _ _ (pid A ∧-> smash_assoc B C D)
      !smash_pmap_unit)^-1 @* _,
    refine pwhisker_left _ _ @* !pcompose_pid,
    apply smash_pmap_unit_counit
Defined.

Definition smash_assoc_pentagon (A B C D : pType) :
    smash_assoc A B (C ∧ D) o* smash_assoc (A ∧ B) C D ==*
    pid A ∧-> smash_assoc B C D o* smash_assoc A (B ∧ C) D o* smash_assoc A B C ∧-> pid D.
Proof.
    refine !pcompose_smash_assoc @* _,
    refine pap (!smash_adjoint_pmap_inv o* !smash_adjoint_pmap_inv o*
      ppcompose_left !smash_adjoint_pmap)
      (phomotopy_path (to_left_inv !smash_adjoint_pmap_inv _)) @* _,
    refine pap (!smash_adjoint_pmap_inv o* !smash_adjoint_pmap_inv)
      (phomotopy_path (!smash_pelim_natural_right _)) @* _,
    symmetry,
    refine !smash_functor_smash_assoc ◾* pwhisker_left _ !smash_assoc_smash_functor @* _ =>
    refine !passoc^-1* @* _,
    refine phomotopy_path (smash_assoc_elim_right_natural_right A B C D _ _) @*
           pap !smash_assoc_elim_right_pequiv (!pcompose_pid @* !pcompose_smash_assoc) @* _,
    apply phomotopy_path,
    apply ap (!smash_adjoint_pmap_inv o !smash_adjoint_pmap_inv o !smash_adjoint_pmap_inv),
    refine ap (ppcompose_left _ o !smash_adjoint_pmap) (to_left_inv !smash_adjoint_pmap_inv _) @ _,
    refine ap (ppcompose_left _) (to_left_inv !smash_adjoint_pmap_inv _) @ _,
    refine ap (ppcompose_left _ o ppcompose_left _) (to_left_inv !smash_adjoint_pmap_inv _) @ _,
    refine ap (ppcompose_left _) ((ppcompose_left_pcompose _ _ _)^-1 @
      ppcompose_left_phomotopy !pinv_pcompose_cancel_left _) @ _,
    refine (ppcompose_left_pcompose _ _ _)^-1 @
      ppcompose_left_phomotopy !pinv_pcompose_cancel_left _ @ _,
    exact ppcompose_left_pcompose _ _ _,
Defined.

  (* Corollary 2: smashing with a suspension *)
Definition smash_susp_elim_pequiv (A B X : pType) :
    ppMap (⅀ A ∧ B) X <~>* ppMap (⅀ (A ∧ B)) X.
  calc
    ppMap (⅀ A ∧ B) X <~>* ppMap (⅀ A) (ppMap B X) : smash_adjoint_pmap (⅀ A) B X
    ... <~>* ppMap A (loops (ppMap B X)) : susp_adjoint_loop A (ppMap B X)
    ... <~>* ppMap A (ppMap B (loops X)) : ppMap_pequiv_ppMap_right (loop_ppMap_pequiv B X)
    ... <~>* ppMap (A ∧ B) (loops X) : smash_adjoint_pmap A B (loops X)
    ... <~>* ppMap (⅀ (A ∧ B)) X : susp_adjoint_loop (A ∧ B) X

Definition smash_susp_elim_natural_right (A B : pType) (f : X ->* X') :
    psquare (smash_susp_elim_pequiv A B X) (smash_susp_elim_pequiv A B X')
            (ppcompose_left f) (ppcompose_left f).
  smash_adjoint_pmap_natural_right (⅀ A) B f @h*
  susp_adjoint_loop_natural_right (ppcompose_left f) @h*
  ppcompose_left_psquare (loop_ppMap_pequiv_natural_right B f) @h*
  (smash_adjoint_pmap_natural_right A B (Ω-> f))^-1ʰ* @h*
  (susp_adjoint_loop_natural_right f)^-1ʰ*

Definition smash_susp_elim_natural_left (X : pType) (f : A' ->* A) (g : B' ->* B) :
    psquare (smash_susp_elim_pequiv A B X) (smash_susp_elim_pequiv A' B' X)
            (ppcompose_right (⅀-> f ∧-> g)) (ppcompose_right (susp_functor (f ∧-> g))).
Proof.
    refine smash_adjoint_pmap_natural_lm X (⅀-> f) g @h*
           _ @h* _ @h*
           (smash_adjoint_pmap_natural_lm (loops X) f g)^-1ʰ* @h*
           (susp_adjoint_loop_natural_left (f ∧-> g))^-1ʰ*,
    rotate 2,
    exact !ppcompose_left_ppcompose_right @v*
      ppcompose_left_psquare (loop_ppMap_pequiv_natural_left X g),
    exact susp_adjoint_loop_natural_left f @v* susp_adjoint_loop_natural_right (ppcompose_right g)
Defined.

Definition susp_smash_rev (A B : pType) : ⅀ (A ∧ B) <~>* ⅀ A ∧ B.
  pyoneda (smash_susp_elim_pequiv A B) (fun X X' f => smash_susp_elim_natural_right A B f)

Definition susp_smash_rev_natural (f : A ->* A') (g : B ->* B') :
    psquare (susp_smash_rev A B) (susp_smash_rev A' B') (⅀-> (f ∧-> g)) (⅀-> f ∧-> g).
Proof.
    refine phomotopy_path (smash_susp_elim_natural_right _ _ _ _) @* _,
    refine pap !smash_susp_elim_pequiv (!pcompose_pid @* !pid_pcompose^-1*) @* _,
    rexact phomotopy_path (smash_susp_elim_natural_left _ f g !pid)^-1
Defined.

Definition susp_smash (A B : pType) : ⅀ A ∧ B <~>* ⅀ (A ∧ B).
  (susp_smash_rev A B)^-1ᵉ*

Definition smash_susp (A B : pType) : A ∧ ⅀ B <~>* ⅀ (A ∧ B).
  calc A ∧ ⅀ B
            <~>* ⅀ B ∧ A  : smash_comm A (⅀ B)
        ... <~>* ⅀(B ∧ A) : susp_smash B A
        ... <~>* ⅀(A ∧ B) : susp_pequiv (smash_comm B A)


Definition smash_susp_natural (f : A ->* A') (g : B ->* B') :
    psquare (smash_susp A B) (smash_susp A' B') (f ∧-> ⅀->g) (⅀-> (f ∧-> g)).
  sorry

Definition susp_smash_move (A B : pType) : ⅀ A ∧ B <~>* A ∧ ⅀ B.
  susp_smash A B @e* (smash_susp A B)^-1ᵉ*

Definition smash_iterate_susp (n : ℕ) (A B : pType) :
    A ∧ iterate_susp n B <~>* iterate_susp n (A ∧ B).
Proof.
    induction n with n e,
    { reflexivity },
    { exact smash_susp A (iterate_susp n B) @e* susp_pequiv e }
Defined.

Definition smash_sphere (A : pType) (n : ℕ) : A ∧ sphere n <~>* iterate_susp n A.
  pequiv.rfl ∧<~> (sphere_pequiv_iterate_susp n) @e*
  smash_iterate_susp n A pbool @e*
  iterate_susp_pequiv n (smash_pbool_pequiv A)

Definition smash_pcircle (A : pType) : A ∧ S¹* <~>* susp A.
  smash_sphere A 1

Definition sphere_smash_sphere (n m : ℕ) : sphere n ∧ sphere m <~>* sphere (n+m).
  smash_sphere (sphere n) m @e*
  iterate_susp_pequiv m (sphere_pequiv_iterate_susp n) @e*
  iterate_susp_iterate_susp_rev m n pbool @e*
  (sphere_pequiv_iterate_susp (n + m))^-1ᵉ*

Defined. smash
