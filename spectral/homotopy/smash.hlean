
import homotopy.smash types.pointed2 .pushout ..pointed

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge is_trunc
     function unit

  (* To prove: Σ(X \* Y) <~> ΣX ∨ ΣY ∨ Σ(X ∧ Y) (notation means suspension, wedge, smash) *)

  (* To prove: Σ(X ∧ Y) <~> X ★ Y (?) (notation means suspension, smash, join) *)

  (* associativity and A ∧ S¹ <~> ΣA is proven in smash_adjoint *)
variables {A A' A'' B B' B'' C C' D E F : pType}

namespace smash

Definition elim_gluel' {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
    (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B, Pmk (point _) b = Pr) (a a' : A) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluel' a a') = Pgl a @ (Pgl a')^-1 :=
  (ap_pp _ _ _) @ whisker_left _ !ap_inv @ !elim_gluel ◾ !elim_gluel⁻²

Definition elim_gluer' {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
    (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B, Pmk (point _) b = Pr) (b b' : B) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluer' b b') = Pgr b @ (Pgr b')^-1 :=
  (ap_pp _ _ _) @ whisker_left _ !ap_inv @ !elim_gluer ◾ !elim_gluer⁻²

Definition elim_gluel'_same {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
    (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B, Pmk (point _) b = Pr) (a : A) :
    elim_gluel' Pgl Pgr a a =
      ap02 (smash.elim Pmk Pl Pr Pgl Pgr) (con.right_inv (gluel a)) @ (con.right_inv (Pgl a))^-1 :=
Proof.
    refine _ @ whisker_right _ (eq_top_of_square ((ap_pp _ _ _)_right_inv_sq))^-1,
    refine _ @ whisker_right _ (concat_p1 _)^-1,
    refine _ @ (concat_pp_p _ _ _)^-1,
    apply whisker_left,
    apply eq_con_inv_of_con_eq, symmetry,
    apply con_right_inv_natural
Defined.

Definition elim_gluer'_same {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
    (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B, Pmk (point _) b = Pr) (b : B) :
    elim_gluer' Pgl Pgr b b =
      ap02 (smash.elim Pmk Pl Pr Pgl Pgr) (con.right_inv (gluer b)) @ (con.right_inv (Pgr b))^-1 :=
Proof.
    refine _ @ whisker_right _ (eq_top_of_square ((ap_pp _ _ _)_right_inv_sq))^-1,
    refine _ @ whisker_right _ (concat_p1 _)^-1,
    refine _ @ (concat_pp_p _ _ _)^-1,
    apply whisker_left,
    apply eq_con_inv_of_con_eq, symmetry,
    apply con_right_inv_natural
Defined.

Definition elim'_gluel'_pt {P : Type} {Pmk : forall a b, P}
    (Pgl : forall a : A, Pmk a (point _) = Pmk (point _) pt) (Pgr : forall b : B, Pmk (point _) b = Pmk (point _) pt)
    (a : A) (ql : Pgl (point _) = idp) (qr : Pgr (point _) = idp) :
    ap (smash.elim' Pmk Pgl Pgr ql qr) (gluel' a (point _)) = Pgl a :=
  !elim_gluel' @ whisker_left _ ql⁻²

Definition elim'_gluer'_pt {P : Type} {Pmk : forall a b, P}
    (Pgl : forall a : A, Pmk a (point _) = Pmk (point _) pt) (Pgr : forall b : B, Pmk (point _) b = Pmk (point _) pt)
    (b : B) (ql : Pgl (point _) = idp) (qr : Pgr (point _) = idp) :
    ap (smash.elim' Pmk Pgl Pgr ql qr) (gluer' b (point _)) = Pgr b :=
  !elim_gluer' @ whisker_left _ qr⁻²

  protectedDefinition rec_eq {A B : pType} {C : Type} {f g : smash A B -> C}
    (Pmk : forall a b, f (smash.mk a b) = g (smash.mk a b))
    (Pl : f auxl = g auxl) (Pr : f auxr = g auxr)
    (Pgl : forall a, square (Pmk a (point _)) Pl (ap f (gluel a)) (ap g (gluel a)))
    (Pgr : forall b, square (Pmk (point _) b) Pr (ap f (gluer b)) (ap g (gluer b))) (x : smash' A B) : f x = g x :=
Proof.
    induction x with a b a b,
    { exact Pmk a b },
    { exact Pl },
    { exact Pr },
    { apply eq_pathover, apply Pgl },
    { apply eq_pathover, apply Pgr }
Defined.

Definition rec_eq_gluel {A B : pType} {C : Type} {f g : smash A B -> C}
    {Pmk : forall a b, f (smash.mk a b) = g (smash.mk a b)}
    {Pl : f auxl = g auxl} {Pr : f auxr = g auxr}
    (Pgl : forall a, square (Pmk a (point _)) Pl (ap f (gluel a)) (ap g (gluel a)))
    (Pgr : forall b, square (Pmk (point _) b) Pr (ap f (gluer b)) (ap g (gluer b))) (a : A) :
      natural_square (smash.rec_eq Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a :=
Proof.
    refine ap square_of_pathover !rec_gluel @ _,
    apply to_right_inv !eq_pathover_equiv_square
Defined.

Definition rec_eq_gluer {A B : pType} {C : Type} {f g : smash A B -> C}
    {Pmk : forall a b, f (smash.mk a b) = g (smash.mk a b)}
    {Pl : f auxl = g auxl} {Pr : f auxr = g auxr}
    (Pgl : forall a, square (Pmk a (point _)) Pl (ap f (gluel a)) (ap g (gluel a)))
    (Pgr : forall b, square (Pmk (point _) b) Pr (ap f (gluer b)) (ap g (gluer b))) (b : B) :
      natural_square (smash.rec_eq Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b :=
Proof.
    refine ap square_of_pathover !rec_gluer @ _,
    apply to_right_inv !eq_pathover_equiv_square
Defined.

  (* the functorial action of the smash product *)
Definition smash_functor' (f : A ->* C) (g : B ->* D) : A ∧ B -> C ∧ D :=
Proof.
    intro x, induction x,
    { exact smash.mk (f a) (g b) },
    { exact auxl },
    { exact auxr },
    { exact ap (smash.mk (f a)) (point_eq g) @ gluel (f a) },
    { exact ap (fun a => smash.mk a (g b)) (point_eq f) @ gluer (g b) }
Defined.

Definition smash_functor (f : A ->* C) (g : B ->* D) : A ∧ B ->* C ∧ D :=
Proof.
    fapply Build_pMap,
    { exact smash_functor' f g } =>
    { exact ap011 smash.mk (point_eq f) (point_eq g) },
Defined.

  infixr ` ∧-> `:65 := smash_functor

Definition functor_gluel (f : A ->* C) (g : B ->* D) (a : A) :
    ap (f ∧-> g) (gluel a) = ap (smash.mk (f a)) (point_eq g) @ gluel (f a) :=
  !elim_gluel

Definition functor_gluer (f : A ->* C) (g : B ->* D) (b : B) :
    ap (f ∧-> g) (gluer b) = ap (fun c => smash.mk c (g b)) (point_eq f) @ gluer (g b) :=
  !elim_gluer

Definition functor_gluel2 {C D : Type} (f : A -> C) (g : B -> D) (a : A) :
    ap (pmap_of_map f (point _) ∧-> pmap_of_map g (point _)) (gluel a) = gluel (f a) :=
Proof.
    refine !elim_gluel @ (concat_1p _)
Defined.

Definition functor_gluer2 {C D : Type} (f : A -> C) (g : B -> D) (b : B) :
    ap (pmap_of_map f (point _) ∧-> pmap_of_map g (point _)) (gluer b) = gluer (g b) :=
Proof.
    refine !elim_gluer @ (concat_1p _)
Defined.

Definition functor_gluel' (f : A ->* C) (g : B ->* D) (a a' : A) :
    ap (f ∧-> g) (gluel' a a') = ap (smash.mk (f a)) (point_eq g) @
      gluel' (f a) (f a') @ (ap (smash.mk (f a')) (point_eq g))^-1 :=
Proof.
    refine !elim_gluel' @ _,
    refine whisker_left _ !con_inv @ _,
    refine (concat_pp_p _ _ _)^-1 @ _, apply whisker_right,
    apply con.assoc
Defined.

Definition functor_gluer' (f : A ->* C) (g : B ->* D) (b b' : B) :
    ap (f ∧-> g) (gluer' b b') = ap (fun c => smash.mk c (g b)) (point_eq f) @
      gluer' (g b) (g b') @ (ap (fun c => smash.mk c (g b')) (point_eq f))^-1 :=
Proof.
    refine !elim_gluer' @ _,
    refine whisker_left _ !con_inv @ _,
    refine (concat_pp_p _ _ _)^-1 @ _, apply whisker_right,
    apply con.assoc
Defined.

  (* the statements of the above rules becomes easier if one of the functions respects the basepoint
     by reflexivity *)


Definition functor_gluel'2 {C D : Type} (f : A -> C) (g : B -> D) (a a' : A) :
    ap (pmap_of_map f (point _) ∧-> pmap_of_map g (point _)) (gluel' a a') = gluel' (f a) (f a') :=
  (ap_pp _ _ _) @ whisker_left _ !ap_inv @ !functor_gluel2 ◾ !functor_gluel2⁻²

Definition functor_gluer'2 {C D : Type} (f : A -> C) (g : B -> D) (b b' : B) :
    ap (pmap_of_map f (point _) ∧-> pmap_of_map g (point _)) (gluer' b b') = gluer' (g b) (g b') :=
  (ap_pp _ _ _) @ whisker_left _ !ap_inv @ !functor_gluer2 ◾ !functor_gluer2⁻²

  lemma functor_gluel'2_same {C D : Type} (f : A -> C) (g : B -> D) (a : A) :
    functor_gluel'2 f g a a =
    ap02 (pmap_of_map f (point _) ∧-> pmap_of_map g (point _)) (con.right_inv (gluel a)) @
    (con.right_inv (gluel (f a)))^-1 :=
Proof.
    refine _ @ whisker_right _ (eq_top_of_square ((ap_pp _ _ _)_right_inv_sq))^-1,
    refine _ @ whisker_right _ (concat_p1 _)^-1,
    refine _ @ (concat_pp_p _ _ _)^-1,
    apply whisker_left,
    apply eq_con_inv_of_con_eq, symmetry,
    apply con_right_inv_natural
Defined.

  lemma functor_gluer'2_same {C D : Type} (f : A -> C) (g : B -> D) (b : B) :
    functor_gluer'2 (pmap_of_map f (point _)) g b b =
    ap02 (pmap_of_map f (point _) ∧-> pmap_of_map g (point _)) (con.right_inv (gluer b)) @
    (con.right_inv (gluer (g b)))^-1 :=
Proof.
    refine _ @ whisker_right _ (eq_top_of_square ((ap_pp _ _ _)_right_inv_sq))^-1,
    refine _ @ whisker_right _ (concat_p1 _)^-1,
    refine _ @ (concat_pp_p _ _ _)^-1,
    apply whisker_left,
    apply eq_con_inv_of_con_eq, symmetry,
    apply con_right_inv_natural
Defined.

Definition smash_functor_pid (A B : pType) :
    pid A ∧-> pid B ==* pid (A ∧ B) :=
Proof.
    fapply Build_pHomotopy,
    { intro x, induction x with a b a b,
      { reflexivity },
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square, exact !functor_gluel @ (concat_1p _) } =>
      { apply eq_pathover_id_right, apply hdeg_square, exact !functor_gluer @ (concat_1p _) }} =>
    { reflexivity }
Defined.

  (* the functorial action of the smash product respects pointed homotopies => and some computation
     rules for this pointed homotopy *)
Definition smash_functor_phomotopy {f f' : A ->* C} {g g' : B ->* D}
    (h₁ : f ==* f') (h₂ : g ==* g') : f ∧-> g ==* f' ∧-> g' :=
Proof.
    induction h₁ using phomotopy_rec_idp,
    induction h₂ using phomotopy_rec_idp,
    reflexivity
Defined.

  infixr ` ∧~ `:78 := smash_functor_phomotopy

  (* a more explicit proof, if we ever need it *)


Definition smash_functor_phomotopy_refl (f : A ->* C) (g : B ->* D) :
    smash_functor_phomotopy (reflexivity f) (reflexivity g) = (reflexivity _) :=
  !phomotopy_rec_idp_refl @ !phomotopy_rec_idp_refl

Definition smash_functor_phomotopy_symm {f₁ f₂ : A ->* C} {g₁ g₂ : B ->* D}
    (h : f₁ ==* f₂) (k : g₁ ==* g₂) :
    smash_functor_phomotopy h^-1* k^-1* = (smash_functor_phomotopy h k)^-1* :=
Proof.
    induction h using phomotopy_rec_idp, induction k using phomotopy_rec_idp,
    exact ap011 smash_functor_phomotopy !refl_symm !refl_symm @ !smash_functor_phomotopy_refl @
      !refl_symm^-1 @ !smash_functor_phomotopy_refl^-1⁻²**
Defined.

Definition smash_functor_phomotopy_trans {f₁ f₂ f₃ : A ->* C} {g₁ g₂ g₃ : B ->* D}
    (h₁ : f₁ ==* f₂) (h₂ : f₂ ==* f₃) (k₁ : g₁ ==* g₂) (k₂ : g₂ ==* g₃) :
    smash_functor_phomotopy (h₁ @* h₂) (k₁ @* k₂) =
    smash_functor_phomotopy h₁ k₁ @* smash_functor_phomotopy h₂ k₂ :=
Proof.
    induction h₁ using phomotopy_rec_idp, induction h₂ using phomotopy_rec_idp,
    induction k₁ using phomotopy_rec_idp, induction k₂ using phomotopy_rec_idp,
    refine ap011 smash_functor_phomotopy !trans_refl !trans_refl @ !trans_refl^-1 @ idp ◾** _ =>
    exact !smash_functor_phomotopy_refl^-1
Defined.

Definition smash_functor_phomotopy_trans_right {f₁ f₂ : A ->* C} {g₁ g₂ g₃ : B ->* D}
    (h₁ : f₁ ==* f₂) (k₁ : g₁ ==* g₂) (k₂ : g₂ ==* g₃) :
    smash_functor_phomotopy h₁ (k₁ @* k₂) =
    smash_functor_phomotopy h₁ k₁ @* smash_functor_phomotopy (reflexivity _) k₂ :=
Proof.
    refine ap (fun x => smash_functor_phomotopy x _) !trans_refl^-1 @ !smash_functor_phomotopy_trans =>
Defined.

Definition smash_functor_phomotopy_phsquare {f₁ f₂ f₃ f₄ : A ->* C} {g₁ g₂ g₃ g₄ : B ->* D}
    {h₁ : f₁ ==* f₂} {h₂ : f₃ ==* f₄} {h₃ : f₁ ==* f₃} {h₄ : f₂ ==* f₄}
    {k₁ : g₁ ==* g₂} {k₂ : g₃ ==* g₄} {k₃ : g₁ ==* g₃} {k₄ : g₂ ==* g₄}
    (p : phsquare h₁ h₂ h₃ h₄) (q : phsquare k₁ k₂ k₃ k₄) :
    phsquare (smash_functor_phomotopy h₁ k₁)
             (smash_functor_phomotopy h₂ k₂)
             (smash_functor_phomotopy h₃ k₃)
             (smash_functor_phomotopy h₄ k₄) :=
  !smash_functor_phomotopy_trans^-1 @ ap011 smash_functor_phomotopy p q @
  !smash_functor_phomotopy_trans

Definition smash_functor_path_pforall (f : A ->* C) {g g' : B ->* D}
    (p : g ==* g') : ap (smash_functor f) (path_pforall p) =
    path_pforall (smash_functor_phomotopy (reflexivity _) p) :=
Proof.
    induction p using phomotopy_rec_idp,
    refine ap02 _ !path_pforall_refl @ _,
    refine !path_pforall_refl^-1 @ _,
    apply ap path_pforall,
    exact !smash_functor_phomotopy_refl^-1
Defined.

Definition smash_functor_path_pforall_left (g : B ->* D) {f f' : A ->* C}
    (p : f ==* f') : ap (fun f => smash_functor f g) (path_pforall p) =
    path_pforall (smash_functor_phomotopy p (reflexivity _)) :=
Proof.
    induction p using phomotopy_rec_idp,
    refine ap02 _ !path_pforall_refl @ _,
    refine !path_pforall_refl^-1 @ _,
    apply ap path_pforall,
    exact !smash_functor_phomotopy_refl^-1
Defined.

  (* the functorial action preserves compositions => the interchange law *)
Definition smash_functor_pcompose_homotopy [unfold 11] {C D E F : Type}
    (f' : C -> E) (f : A -> C) (g' : D -> F) (g : B -> D) :
    (pmap_of_map f' (f (point _)) o* pmap_of_map f (point _)) ∧-> (pmap_of_map g' (g (point _)) o* pmap_of_map g (point _)) ~
    (pmap_of_map f' (f (point _)) ∧-> pmap_of_map g' (g (point _))) o* (pmap_of_map f (point _) ∧-> pmap_of_map g (point _)) :=
Proof.
    intro x, induction x with a b a b,
    { reflexivity },
    { reflexivity },
    { reflexivity },
    { apply eq_pathover, refine !functor_gluel2 @ph _ => esimp,
      refine _ @hp (ap_compose (_ ∧->  _) _ _)^-1,
      refine _ @hp ap02 _ !functor_gluel2^-1 => refine _ @hp !functor_gluel2^-1 => exact hrfl },
    { apply eq_pathover, refine !functor_gluer2 @ph _ => esimp,
      refine _ @hp (ap_compose (_ ∧-> _) _ _)^-1,
      refine _ @hp ap02 _ !functor_gluer2^-1 => refine _ @hp !functor_gluer2^-1 => exact hrfl }
Defined.

Definition smash_functor_pcompose (f' : C ->* E) (f : A ->* C) (g' : D ->* F) (g : B ->* D) :
    (f' o* f) ∧-> (g' o* g) ==* f' ∧-> g' o* f ∧-> g :=
Proof.
    induction C with C, induction D with D, induction E with E, induction F with F,
    induction f with f f₀, induction f' with f' f'₀, induction g with g g₀,
    induction g' with g' g'₀, esimp at *,
    induction f₀, induction f'₀, induction g₀, induction g'₀,
    fapply Build_pHomotopy,
    { rexact smash_functor_pcompose_homotopy f' f g' g } =>
    { reflexivity }
Defined.

Definition smash_functor_split (f : A ->* C) (g : B ->* D) :
    f ∧-> g ==* f ∧-> pid D o* pid A ∧-> g :=
  smash_functor_phomotopy !pcompose_pid^-1* !pid_pcompose^-1* @* !smash_functor_pcompose

Definition smash_functor_split_rev (f : A ->* C) (g : B ->* D) :
    f ∧-> g ==* pid C ∧-> g o* f ∧-> pid B :=
  smash_functor_phomotopy !pid_pcompose^-1* !pcompose_pid^-1* @* !smash_functor_pcompose

  (* An alternative proof which doesn't start by applying inductions, so which is more explicit *)



Definition smash_functor_pid_pcompose (A : pType) (g' : C ->* D) (g : B ->* C)
    : pid A ∧-> (g' o* g) ==* pid A ∧-> g' o* pid A ∧-> g :=
  smash_functor_phomotopy !pid_pcompose^-1* (reflexivity _) @* !smash_functor_pcompose

Definition smash_functor_pcompose_pid (B : pType) (f' : C ->* D) (f : A ->* C)
    : (f' o* f) ∧-> pid B ==* f' ∧-> (pid B) o* f ∧-> (pid B) :=
  smash_functor_phomotopy (reflexivity _) !pid_pcompose^-1* @* !smash_functor_pcompose

  (* composing commutes with applying homotopies *)
Definition smash_functor_pcompose_phomotopy {f₂ f₂' : C ->* E} {f f' : A ->* C} {g₂ g₂' : D ->* F}
    {g g' : B ->* D} (h₂ : f₂ ==* f₂') (h₁ : f ==* f') (k₂ : g₂ ==* g₂') (k₁ : g ==* g') :
    phsquare (smash_functor_pcompose f₂ f g₂ g)
             (smash_functor_pcompose f₂' f' g₂' g')
             (smash_functor_phomotopy (h₂ ◾* h₁) (k₂ ◾* k₁))
             (smash_functor_phomotopy h₂ k₂ ◾* smash_functor_phomotopy h₁ k₁) :=
Proof.
    induction h₁ using phomotopy_rec_idp, induction h₂ using phomotopy_rec_idp,
    induction k₁ using phomotopy_rec_idp, induction k₂ using phomotopy_rec_idp,
    refine (ap011 smash_functor_phomotopy !pcompose2_refl !pcompose2_refl @
      !smash_functor_phomotopy_refl) @ph** phvrfl @hp**
      (ap011 pcompose2 !smash_functor_phomotopy_refl !smash_functor_phomotopy_refl @
      !pcompose2_refl)^-1,
Defined.

Definition smash_functor_pid_pcompose_phomotopy_right (g₂ : D ->* E) {g g' : B ->* D}
    (k : g ==* g') :
    phsquare (smash_functor_pid_pcompose A g₂ g)
             (smash_functor_pid_pcompose A g₂ g')
             (smash_functor_phomotopy (reflexivity _) (pwhisker_left g₂ k))
             (pwhisker_left (pid A ∧-> g₂) (smash_functor_phomotopy (reflexivity _) k)) :=
Proof.
    refine smash_functor_phomotopy_phsquare _ _ @h** !smash_functor_pcompose_phomotopy @hp**
      ((ap (pwhisker_right _) !smash_functor_phomotopy_refl) ◾** idp @ !pcompose2_refl_left) =>
      exact (!pcompose2_refl @ph** phvrfl)^-1ʰ**,
      exact (phhrfl @hp** !pcompose2_refl_left^-1)
Defined.

  section
  variables {A₀₀ A₂₀ A₀₂ A₂₂ : pType} {B₀₀ B₂₀ B₀₂ B₂₂ : pType}
            {f₁₀ : A₀₀ ->* A₂₀} {f₀₁ : A₀₀ ->* A₀₂} {f₂₁ : A₂₀ ->* A₂₂} {f₁₂ : A₀₂ ->* A₂₂}
            {g₁₀ : B₀₀ ->* B₂₀} {g₀₁ : B₀₀ ->* B₀₂} {g₂₁ : B₂₀ ->* B₂₂} {g₁₂ : B₀₂ ->* B₂₂}

  (* applying the functorial action of smash to squares of pointed maps *)
Definition smash_functor_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare g₁₀ g₁₂ g₀₁ g₂₁) :
    psquare (f₁₀ ∧-> g₁₀) (f₁₂ ∧-> g₁₂) (f₀₁ ∧-> g₀₁) (f₂₁ ∧-> g₂₁) :=
  !smash_functor_pcompose^-1* @* smash_functor_phomotopy p q @* !smash_functor_pcompose
Defined.


  (* f ∧ g is a pointed equivalence if f and g are *)
Definition smash_functor_using_pushout (f : A ->* C) (g : B ->* D) : A ∧ B -> C ∧ D :=
Proof.
    fapply pushout.functor (sum_functor f g) (prod_functor f g) id =>
    { intro v, induction v with a b,
      exact prod_eq idp (point_eq g),
      exact prod_eq (point_eq f) idp },
    { intro v, induction v with a b: reflexivity }
Defined.

Definition smash_functor_homotopy_pushout_functor (f : A ->* C) (g : B ->* D) :
    f ∧-> g == smash_functor_using_pushout f g :=
Proof.
    intro x, induction x,
    { reflexivity },
    { reflexivity },
    { reflexivity },
    { apply eq_pathover, refine !elim_gluel @ph _ @hp !pushout.elim_glue^-1,
      apply hdeg_square, esimp, apply whisker_right, exact !ap_ap011^-1 },
    { apply eq_pathover, refine !elim_gluer @ph _ @hp !pushout.elim_glue^-1,
      apply hdeg_square, esimp, apply whisker_right, exact !ap_ap011^-1 }
Defined.

  local attribute is_equiv_sum_functor [instance]
Definition smash_pequiv (f : A <~>* C) (g : B <~>* D) : A ∧ B <~>* C ∧ D :=
Proof.
    fapply pequiv_of_pmap (f ∧-> g),
    refine homotopy_closed _ (smash_functor_homotopy_pushout_functor f g)^-1ʰᵗʸ _ =>
    apply pushout.is_equiv_functor
Defined.

  infixr ` ∧<~> `:80 := smash_pequiv


Definition smash_pequiv_left (B : pType) (f : A <~>* C) : A ∧ B <~>* C ∧ B :=
  f ∧<~> pequiv.rfl

Definition smash_pequiv_right (A : pType) (g : B <~>* D) : A ∧ B <~>* A ∧ D :=
  pequiv.rfl ∧<~> g

  (* f ∧ g is constant if f is constant *)
Definition smash_functor_pconst_left_homotopy {B' : Type} (f : B -> B') (x : A ∧ B) :
    (pconst A A' ∧-> pmap_of_map f (point _)) x = (point _) :=
Proof.
    induction x with a b a b,
    { exact gluer' (f b) (point _) },
    { exact (gluel (point _))^-1 },
    { exact (gluer (point _))^-1ᵖ },
    { apply eq_pathover, note x := functor_gluel2 (fun x : A => Point A') f a,
      refine x @ph _, refine _ @hp (ap_pp _ _ _)stant^-1, apply square_of_eq,
      rexact con.right_inv (gluer (f (point _))) @ (con.right_inv (gluel (point _)))^-1 },
    { apply eq_pathover, note x := functor_gluer2 (fun x : A => Point A') f b,
      refine x @ph _, refine _ @hp (ap_pp _ _ _)stant^-1, apply square_of_eq, reflexivity }
Defined.

Definition smash_functor_pconst_left (f : B ->* B') : pconst A A' ∧-> f ==* pconst (A ∧ B) (A' ∧ B') :=
Proof.
    induction B' with B', induction f with f f₀, esimp at *, induction f₀,
    fapply Build_pHomotopy,
    { exact smash_functor_pconst_left_homotopy f } =>
    { rexact con.right_inv (gluer (f (point _))) }
Defined.

Definition smash_functor_pconst_left_phomotopy {f f' : B ->* B'} (p : f ==* f') :
    reflexivity (pconst A A') ∧~ p @* smash_functor_pconst_left f' = smash_functor_pconst_left f :=
Proof.
    induction p using phomotopy_rec_idp,
    exact !smash_functor_phomotopy_refl ◾** idp @ !refl_trans
Defined.

  (* This makes smash_functor into a pointed map (B ->* B') ->* (A ∧ B ->* A ∧ B') *)

Definition smash_functor_left (A A' B : pType) :
    ppMap A A' ->* ppMap (A ∧ B) (A' ∧ B) :=
  Build_pMap (fun f => f ∧-> pid B) (path_pforall (smash_functor_pconst_left (pid B)))

  (* We want to show that smash_functor_left is natural in A => B and C.

     For this we need two coherence rules. Given the function h := (f' o f) ∧-> (g' o g) and suppose
     that either f' or f is constant. There are two ways to show that h is constant: either by using
     exchange, or directly. We need to show that these two proofs result in the same pointed
     homotopy. First we do the case where f is constant *)

  privateDefinition my_squarel {A : Type} {a₁ a₂ a₃ : A} (p₁ : a₁ = a₃) (p₂ : a₂ = a₃) :
    square (p₁ @ p₂^-1) p₂^-1 p₁ idp :=
  proof square_of_eq idp qed

  privateDefinition my_squarer {A : Type} {a₁ a₂ a₃ : A} (p₁ : a₁ = a₃) (p₂ : a₁ = a₂) :
    square (p₁ @ p₁^-1) p₂^-1 p₂ idp :=
  proof square_of_eq (con.right_inv p₁ @ (con.right_inv p₂)^-1) qed

  privateDefinition my_cube_fillerl {B C : Type} {g : B -> C} {fa₁ fa₂ b₀ : B}
    {pa₁ : fa₁ = b₀} {pa₂ : fa₂ = b₀} {qa₁ : g (fa₁) = g b₀} {qa₂ : g (fa₂) = g b₀}
    (ra₁ : ap g (pa₁) = qa₁) (ra₂ : ap g (pa₂) = qa₂) :
    cube (hrfl @hp (ra₁)^-1) hrfl
         (my_squarel (qa₁) (qa₂)) (aps g (my_squarel (pa₁) (pa₂)))
         (hrfl @hp ((ap_pp _ _ _) @ whisker_left _ !ap_inv @ (ra₁) ◾ (ra₂)⁻²)^-1)
           (hrfl @hp (ra₂)⁻²^-1 @hp !ap_inv^-1) :=
Proof.
    induction ra₂, induction ra₁, induction pa₂, induction pa₁, exact idc
Defined.

  privateDefinition my_cube_fillerr {B C : Type} {g : B -> C} {b₀ bl br : B}
    {pl : b₀ = bl} {pr : b₀ = br} {ql : g b₀ = g bl} {qr : g b₀ = g br}
    (sl : ap g pl = ql) (sr : ap g pr = qr) :
    cube (hrfl @hp sr^-1) hrfl
         (my_squarer ql qr) (aps g (my_squarer pl pr))
         (hrfl @hp ((ap_pp _ _ _) @ whisker_left _ !ap_inv @ sl ◾ sl⁻²)^-1)
         (hrfl @hp sr⁻²^-1 @hp !ap_inv^-1) :=
Proof.
    induction sr, induction sl, induction pr, induction pl, exact idc
Defined.

Definition smash_functor_pcompose_pconst2_homotopy {A A' A'' B B' B'' : Type}
    (a₀ : A) (b₀ : B) (a₀' : A') (f' : A' -> A'') (g' : B' -> B'') (g : B -> B')
    (x : pointed.MK A a₀ ∧ pointed.MK B b₀) :
    square (smash_functor_pcompose_homotopy f' (fun a => a₀') g' g x)
    idp
    (smash_functor_pconst_left_homotopy (fun a => g' (g a)) x)
    (ap (smash_functor' (Build_pMap f' (refl (f' a₀'))) (Build_pMap g' (refl (g' (g b₀)))))
      (smash_functor_pconst_left_homotopy g x)) :=
Proof.
    induction x with a b a b,
    { refine _ @hp (functor_gluer'2 f' g' (g b) (g b₀))^-1 => exact hrfl },
    { refine _ @hp !ap_inv^-1, refine _ @hp !functor_gluel2⁻²^-1 => exact hrfl },
    { refine _ @hp !ap_inv^-1, refine _ @hp !functor_gluer2⁻²^-1 => exact hrfl },
    { exact abstract begin apply square_pathover,
      refine !rec_eq_gluel @p1 _ @1p !natural_square_refl^-1,
      refine !rec_eq_gluel @p2 _ @2p !natural_square_ap_fn^-1,
      apply whisker001, apply whisker021,
      apply move201, refine _ @1p !eq_hconcat_hdeg_square^-1,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine ap (hconcat_eq _) !ap_inv @p1 _ @2p (ap (aps _) !rec_eq_gluel @ !aps_eq_hconcat)^-1,
      apply whisker021, refine _ @2p !aps_hconcat_eq^-1, apply move221,
      refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine _ @1p ap hdeg_square (eq_bot_of_square (transpose !ap02_ap_constant)),
      apply my_cube_fillerr end end },
    { exact abstract begin apply square_pathover,
      refine !rec_eq_gluer @p1 _ @1p !natural_square_refl^-1,
      refine !rec_eq_gluer @p2 _ @2p !natural_square_ap_fn^-1,
      apply whisker001, apply whisker021,
      apply move201, refine _ @1p !eq_hconcat_hdeg_square^-1,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine ap (hconcat_eq _) !ap_inv @p1 _ @2p (ap (aps _) !rec_eq_gluer @ !aps_eq_hconcat)^-1,
      apply whisker021, refine _ @2p !aps_hconcat_eq^-1, apply move221,
      refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine _ @1p ap hdeg_square (eq_bot_of_square (transpose !ap02_ap_constant)),
      apply my_cube_fillerl end end }
Defined.

Definition smash_functor_pcompose_pconst2 (f' : A' ->* A'') (g' : B' ->* B'') (g : B ->* B') :
    phsquare (smash_functor_pcompose f' (pconst A A') g' g)
             (smash_functor_pconst_left (g' o* g))
             (smash_functor_phomotopy (pcompose_pconst f') (reflexivity _))
             (pwhisker_left (f' ∧-> g') (smash_functor_pconst_left g) @*
               pcompose_pconst (f' ∧-> g')) :=
Proof.
    induction A with A a₀, induction B with B b₀,
    induction A' with A' a₀', induction B' with B' b₀',
    induction A'' with A'' a₀'', induction B'' with B'' b₀'',
    induction f' with f' f'₀, induction g' with g' g₀', induction g with g g₀,
    esimp at *, induction f'₀, induction g₀', induction g₀,
    refine !smash_functor_phomotopy_refl @ph** _ => refine _ @ !refl_trans^-1,
    fapply phomotopy_eq,
    { intro x, refine eq_of_square _ @ (concat_p1 _),
      exact smash_functor_pcompose_pconst2_homotopy a₀ b₀ a₀' f' g' g x } =>
    { refine _ @ (concat_1p _)^-1,
      refine whisker_right _ (!whisker_right_idp @ !eq_of_square_hrfl_hconcat_eq) @ _,
      refine (concat_pp_p _ _ _) @ _, apply con_eq_of_eq_inv_con,
      refine whisker_right _ _ @ _, rotate 1, rexact functor_gluer'2_same f' g' (g b₀) =>
      refine !inv_con_cancel_right @ _,
      refine !whisker_left_idp^-1 @ _,
      refine (concat_p1 _) @ _,
      apply whisker_left,
      apply ap (whisker_left idp),
      exact ((concat_1p _) @ (concat_1p _) @ !whisker_right_idp @ (concat_1p _))^-1 }
Defined.

  (* a version where the left maps are identities *)
Definition smash_functor_pcompose_pconst2_pid (f' : A' ->* A'') :
    phsquare (smash_functor_pcompose_pid B f' (pconst A A'))
             (smash_functor_pconst_left (pid B))
             (pcompose_pconst f' ∧~ (reflexivity _))
             (pwhisker_left (f' ∧-> pid B) (smash_functor_pconst_left (pid B)) @*
               pcompose_pconst (f' ∧-> pid B)) :=
  (!smash_functor_phomotopy_refl ◾** idp @ !refl_trans) @pv**
  smash_functor_pcompose_pconst2 f' (pid B) (pid B)

  (* a small rewrite of the previous *)

  (* if f' is constant *)
Definition smash_functor_pcompose_pconst1_homotopy [unfold 13] {A A' A'' B B' B'' : Type}
    (a₀ : A) (b₀ : B) (a₀'' : A'') (f : A -> A') (g' : B' -> B'') (g : B -> B')
    (x : pointed.MK A a₀ ∧ pointed.MK B b₀) :
    square (smash_functor_pcompose_homotopy (fun a' => a₀'') f g' g x)
    idp
    (smash_functor_pconst_left_homotopy (fun a => g' (g a)) x)
    (smash_functor_pconst_left_homotopy g'
      ((pmap_of_map f a₀ ∧-> pmap_of_map g b₀) x)) :=
Proof.
    induction x with a b a b,
    { exact hrfl },
    { exact hrfl },
    { exact hrfl },
    { exact abstract begin apply square_pathover,
      refine !rec_eq_gluel @p1 _ @1p !natural_square_refl^-1,
      refine !rec_eq_gluel @p2 _ @2p
        (natural_square_compose (smash_functor_pconst_left_homotopy g') _ _)^-1ᵖ =>
      apply whisker001, apply whisker021,
      apply move201, refine _ @1p !eq_hconcat_hdeg_square^-1,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine ap (hconcat_eq _) !ap_inv @p1 _ @2p (natural_square_eq2 _ !functor_gluel2)^-1ᵖ =>
      apply whisker021,
      refine _ @1p ap hdeg_square (eq_of_square ((ap_pp _ _ _)stant_compose^-1ʰ) @ (concat_1p _))^-1,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine _ @2p !rec_eq_gluel^-1, apply whisker021,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine _ @1p ap hdeg_square (eq_bot_of_square (transpose !ap02_constant)),
      exact rfl2 end end },
    { exact abstract begin apply square_pathover,
      refine !rec_eq_gluer @p1 _ @1p !natural_square_refl^-1,
      refine !rec_eq_gluer @p2 _ @2p
        (natural_square_compose (smash_functor_pconst_left_homotopy g') _ _)^-1ᵖ =>
      apply whisker001, apply whisker021,
      apply move201, refine _ @1p !eq_hconcat_hdeg_square^-1,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine ap (hconcat_eq _) !ap_inv @p1 _ @2p (natural_square_eq2 _ !functor_gluer2)^-1ᵖ =>
      apply whisker021,
      refine _ @1p ap hdeg_square (eq_of_square ((ap_pp _ _ _)stant_compose^-1ʰ) @ (concat_1p _))^-1,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine _ @2p !rec_eq_gluer^-1, apply whisker021,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine _ @1p ap hdeg_square (eq_bot_of_square (transpose !ap02_constant)),
      exact rfl2 end end },
Defined.

Definition smash_functor_pcompose_pconst1 (f : A ->* A') (g' : B' ->* B'') (g : B ->* B') :
    phsquare (smash_functor_pcompose (pconst A' A'') f g' g)
             (smash_functor_pconst_left (g' o* g))
             (pconst_pcompose f ∧~ (reflexivity _))
             (pwhisker_right (f ∧-> g) (smash_functor_pconst_left g') @*
               pconst_pcompose (f ∧-> g)) :=
Proof.
    induction A with A a₀, induction B with B b₀,
    induction A' with A' a₀', induction B' with B' b₀',
    induction A'' with A'' a₀'', induction B'' with B'' b₀'',
    induction f with f f₀, induction g' with g' g₀', induction g with g g₀,
    esimp at *, induction f₀, induction g₀', induction g₀,
    refine !smash_functor_phomotopy_refl @ph** _ => refine _ @ !refl_trans^-1,
    fapply phomotopy_eq,
    { intro x, refine eq_of_square (smash_functor_pcompose_pconst1_homotopy a₀ b₀ a₀'' f g' g x) } =>
    { refine whisker_right _ (!whisker_right_idp @ !eq_of_square_hrfl) @ _,
      have H : forall {A : Type} {a a' : A} (p : a = a'),
               idp_con (p @ p^-1) @ con.right_inv p = idp @
               whisker_left idp (idp @ (idp @ proof whisker_right idp (idp_con (p @ p^-1ᵖ))^-1ᵖ qed @
                 whisker_left idp (con.right_inv p))), by intros; induction p; reflexivity,
      rexact H (gluer (g' (g b₀))) }
Defined.

  (* a version where the left maps are identities *)
Definition smash_functor_pcompose_pconst1_pid (f : A ->* A') :
    phsquare (smash_functor_pcompose_pid B (pconst A' A'') f)
             (smash_functor_pconst_left (pid B))
             (pconst_pcompose f ∧~ (reflexivity _))
             (pwhisker_right (f ∧-> pid B) (smash_functor_pconst_left (pid B)) @*
               pconst_pcompose (f ∧-> pid B)) :=
  (!smash_functor_phomotopy_refl ◾** idp @ !refl_trans) @pv**
  smash_functor_pcompose_pconst1 f (pid B) (pid B)

  (* Using these lemmas we show that smash_functor_left is natural in all arguments *)

Definition smash_functor_left_natural_left (B C : pType) (f : A' ->* A) :
    psquare (smash_functor_left A B C) (smash_functor_left A' B C)
            (ppcompose_right f) (ppcompose_right (f ∧-> pid C)) :=
Proof.
    refine _^-1*,
    fapply phomotopy_mk_ppMap,
    { intro g, exact smash_functor_pcompose_pid C g f } =>
    { refine idp ◾** (!phomotopy_path_con @ (ap phomotopy_path !pcompose_right_path_pforall @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy) @ _ ,
      refine _ @ (!phomotopy_path_con @ (ap phomotopy_path !smash_functor_path_pforall_left @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy)^-1,
      apply smash_functor_pcompose_pconst1_pid }
Defined.

Definition smash_functor_left_natural_middle (A C : pType) (f : B ->* B') :
    psquare (smash_functor_left A B C) (smash_functor_left A B' C)
            (ppcompose_left f) (ppcompose_left (f ∧-> pid C)) :=
Proof.
    refine _^-1*,
    fapply phomotopy_mk_ppMap,
    { exact smash_functor_pcompose_pid C f } =>
    { refine idp ◾** (!phomotopy_path_con @ (ap phomotopy_path !pcompose_left_path_pforall @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy) @ _ ,
      refine _ @ (!phomotopy_path_con @ (ap phomotopy_path !smash_functor_path_pforall_left @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy)^-1,
      apply smash_functor_pcompose_pconst2_pid }
Defined.

Definition smash_functor_left_natural_right (A B : pType) (f : C ->* C') :
    psquare (smash_functor_left A B C) (ppcompose_right (pid A ∧-> f))
            (smash_functor_left A B C') (ppcompose_left (pid B ∧-> f)) :=
Proof.
    refine _^-1*,
    fapply phomotopy_mk_ppMap,
    { intro g, exact smash_functor_psquare proof (reflexivity _) qed proof (reflexivity _) qed } =>
    { esimp,
      refine idp ◾** (!phomotopy_path_con @ (ap phomotopy_path !pcompose_left_path_pforall @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy) @ _ ,
      refine _ @ (!phomotopy_path_con @ (ap phomotopy_path !pcompose_right_path_pforall @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy)^-1,
      apply eq_of_phsquare,
      refine (phmove_bot_of_left _ !smash_functor_pcompose_pconst1^-1ʰ**) @h**
        (!smash_functor_phomotopy_refl @pv** !phhrfl) @h** !smash_functor_pcompose_pconst2 @vp** _ =>
      refine !trans_assoc @ !trans_assoc @ idp ◾** _ @ !trans_refl,
      refine idp ◾** !refl_trans @ !trans_left_inv }
Defined.

Definition smash_functor_left_natural_middle_phomotopy (A C : pType) {f f' : B ->* B'}
    (p : f ==* f') : smash_functor_left_natural_middle A C f =
    ppcompose_left_phomotopy p @ph* smash_functor_left_natural_middle A C f' @hp*
    ppcompose_left_phomotopy (p ∧~ (reflexivity _)) :=
Proof.
    induction p using phomotopy_rec_idp,
    symmetry,
    refine !ppcompose_left_phomotopy_refl ◾ph* idp ◾hp*
     (ap ppcompose_left_phomotopy !smash_functor_phomotopy_refl @
     !ppcompose_left_phomotopy_refl) @ _,
    exact !rfl_phomotopy_hconcat @ !hconcat_phomotopy_rfl
Defined.

  (* the following is not really used, but a symmetric version of the natural equivalence
     smash_functor_left *)
  (* f ∧ g is constant if g is constant *)
Definition smash_functor_pconst_right_homotopy {C : Type} (f : A -> C) (x : A ∧ B) :
    (pmap_of_map f (point _) ∧-> pconst B D) x = (point _) :=
Proof.
    induction x with a b a b,
    { exact gluel' (f a) (point _) },
    { exact (gluel (point _))^-1 },
    { exact (gluer (point _))^-1 },
    { apply eq_pathover, note x := functor_gluel2 f (fun x : B => Point D) a, esimp [pconst] at *,
      refine x @ph _, refine _ @hp (ap_pp _ _ _)stant^-1, apply square_of_eq, reflexivity },
    { apply eq_pathover, note x := functor_gluer2 f (fun x : B => Point D) b, esimp [pconst] at *,
      refine x @ph _, refine _ @hp (ap_pp _ _ _)stant^-1, apply square_of_eq,
      rexact con.right_inv (gluel (f (point _))) @ (con.right_inv (gluer (point _)))^-1 }
Defined.

Definition smash_functor_pconst_right (f : A ->* C) :
    f ∧-> (pconst B D) ==* pconst (A ∧ B) (C ∧ D) :=
Proof.
    induction C with C, induction f with f f₀, esimp at *, induction f₀,
    fapply Build_pHomotopy,
    { exact smash_functor_pconst_right_homotopy f } =>
    { rexact con.right_inv (gluel (f (point _))) }
Defined.

Definition smash_functor_pconst_right_phomotopy {f f' : A ->* C} (p : f ==* f') :
    smash_functor_phomotopy p (reflexivity (pconst B D)) @* smash_functor_pconst_right f' =
    smash_functor_pconst_right f :=
Proof.
    induction p using phomotopy_rec_idp,
    exact !smash_functor_phomotopy_refl ◾** idp @ !refl_trans
Defined.

  (* This makes smash_functor into a pointed map (B ->* B') ->* (A ∧ B ->* A ∧ B') *)

Definition smash_functor_right (A B C : pType) :
    ppMap B C ->* ppMap (A ∧ B) (A ∧ C) :=
  Build_pMap (smash_functor (pid A)) (path_pforall (smash_functor_pconst_right (pid A)))

  (* We want to show that smash_functor_right is natural in A => B and C.

     For this we need two coherence rules. Given the function h := (f' o f) ∧-> (g' o g) and suppose
     that either g' or g is constant. There are two ways to show that h is constant: either by using
     exchange, or directly. We need to show that these two proofs result in the same pointed
     homotopy. First we do the case where g is constant *)

Definition smash_functor_pcompose_pconst4_homotopy {A B C D E F : Type}
    (a₀ : A) (b₀ : B) (d₀ : D) (f' : C -> E) (f : A -> C) (g : D -> F)
    (x : pointed.MK A a₀ ∧ pointed.MK B b₀) :
    square (smash_functor_pcompose_homotopy f' f g (fun a => d₀) x)
    idp
    (smash_functor_pconst_right_homotopy (fun a => f' (f a)) x)
    (ap (smash_functor' (Build_pMap f' (refl (f' (f a₀)))) (Build_pMap g (refl (g d₀))))
      (smash_functor_pconst_right_homotopy f x)) :=
Proof.
    induction x with a b a b,
    { refine _ @hp (functor_gluel'2 f' g (f a) (f a₀))^-1 => exact hrfl },
    { refine _ @hp !ap_inv^-1, refine _ @hp !functor_gluel2⁻²^-1 => exact hrfl },
    { refine _ @hp !ap_inv^-1, refine _ @hp !functor_gluer2⁻²^-1 => exact hrfl },
    { exact abstract begin apply square_pathover,
      refine !rec_eq_gluel @p1 _ @1p !natural_square_refl^-1,
      refine !rec_eq_gluel @p2 _ @2p !natural_square_ap_fn^-1,
      apply whisker001, apply whisker021,
      apply move201, refine _ @1p !eq_hconcat_hdeg_square^-1,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine ap (hconcat_eq _) !ap_inv @p1 _ @2p (ap (aps _) !rec_eq_gluel @ !aps_eq_hconcat)^-1,
      apply whisker021, refine _ @2p !aps_hconcat_eq^-1, apply move221,
      refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine _ @1p ap hdeg_square (eq_bot_of_square (transpose !ap02_ap_constant)),
      apply my_cube_fillerl end end },
    { exact abstract begin apply square_pathover,
      refine !rec_eq_gluer @p1 _ @1p !natural_square_refl^-1,
      refine !rec_eq_gluer @p2 _ @2p !natural_square_ap_fn^-1,
      apply whisker001, apply whisker021,
      apply move201, refine _ @1p !eq_hconcat_hdeg_square^-1,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine ap (hconcat_eq _) !ap_inv @p1 _ @2p (ap (aps _) !rec_eq_gluer @ !aps_eq_hconcat)^-1,
      apply whisker021, refine _ @2p !aps_hconcat_eq^-1, apply move221,
      refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine _ @1p ap hdeg_square (eq_bot_of_square (transpose !ap02_ap_constant)),
      apply my_cube_fillerr end end }
Defined.

Definition smash_functor_pcompose_pconst4 (f' : C ->* E) (f : A ->* C) (g : D ->* F) :
    phsquare (smash_functor_pcompose f' f g (pconst B D))
             (smash_functor_pconst_right (f' o* f))
             (smash_functor_phomotopy (reflexivity _) (pcompose_pconst g))
             (pwhisker_left (f' ∧-> g) (smash_functor_pconst_right f) @*
               pcompose_pconst (f' ∧-> g)) :=
Proof.
    induction A with A a₀, induction B with B b₀,
    induction E with E e₀, induction C with C c₀, induction F with F x₀, induction D with D d₀,
    induction f' with f' f'₀, induction f with f f₀, induction g with g g₀,
    esimp at *, induction f'₀, induction f₀, induction g₀,
    refine !smash_functor_phomotopy_refl @ph** _ => refine _ @ !refl_trans^-1,
    fapply phomotopy_eq,
    { intro x, refine eq_of_square _ @ (concat_p1 _),
      exact smash_functor_pcompose_pconst4_homotopy a₀ b₀ d₀ f' f g x => },
    { refine _ @ (concat_1p _)^-1,
      refine whisker_right _ (!whisker_right_idp @ !eq_of_square_hrfl_hconcat_eq) @ _,
      refine (concat_pp_p _ _ _) @ _, apply con_eq_of_eq_inv_con,
      refine whisker_right _ _ @ _, rotate 1, rexact functor_gluel'2_same f' g (f a₀) =>
      refine !inv_con_cancel_right @ _,
      refine !whisker_left_idp^-1 @ _,
      refine (concat_p1 _) @ _,
      apply whisker_left,
      apply ap (whisker_left idp),
      exact ((concat_1p _) @ (concat_1p _) @ !whisker_right_idp @ (concat_1p _))^-1 }
Defined.

  (* a version where the left maps are identities *)
Definition smash_functor_pcompose_pconst4_pid (g : D ->* F) :
    phsquare (smash_functor_pid_pcompose A g (pconst B D))
             (smash_functor_pconst_right (pid A))
             (smash_functor_phomotopy (reflexivity _) (pcompose_pconst g))
             (pwhisker_left (pid A ∧-> g) (smash_functor_pconst_right (pid A)) @*
               pcompose_pconst (pid A ∧-> g)) :=
  (!smash_functor_phomotopy_refl ◾** idp @ !refl_trans) @pv**
  smash_functor_pcompose_pconst4 (pid A) (pid A) g

  (* a small rewrite of the previous *)

  (* if g' is constant *)
Definition smash_functor_pcompose_pconst3_homotopy [unfold 13] {A B C D E F : Type}
    (a₀ : A) (b₀ : B) (x₀ : F) (f' : C -> E) (f : A -> C) (g : B -> D)
    (x : pointed.MK A a₀ ∧ pointed.MK B b₀) :
    square (smash_functor_pcompose_homotopy f' f (fun a => x₀) g x)
    idp
    (smash_functor_pconst_right_homotopy (fun a => f' (f a)) x)
    (smash_functor_pconst_right_homotopy f'
      (smash_functor (pmap_of_map f a₀) (pmap_of_map g b₀) x)) :=
Proof.
    induction x with a b a b,
    { exact hrfl },
    { exact hrfl },
    { exact hrfl },
    { exact abstract begin apply square_pathover,
      refine !rec_eq_gluel @p1 _ @1p !natural_square_refl^-1,
      refine !rec_eq_gluel @p2 _ @2p
        (natural_square_compose (smash_functor_pconst_right_homotopy f') _ _)^-1ᵖ =>
      apply whisker001, apply whisker021,
      apply move201, refine _ @1p !eq_hconcat_hdeg_square^-1,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine ap (hconcat_eq _) !ap_inv @p1 _ @2p (natural_square_eq2 _ !functor_gluel2)^-1ᵖ =>
      apply whisker021,
      refine _ @1p ap hdeg_square (eq_of_square ((ap_pp _ _ _)stant_compose^-1ʰ) @ (concat_1p _))^-1,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine _ @2p !rec_eq_gluel^-1, apply whisker021,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine _ @1p ap hdeg_square (eq_bot_of_square (transpose !ap02_constant)),
      exact rfl2 end end },
    { exact abstract begin apply square_pathover,
      refine !rec_eq_gluer @p1 _ @1p !natural_square_refl^-1,
      refine !rec_eq_gluer @p2 _ @2p
        (natural_square_compose (smash_functor_pconst_right_homotopy f') _ _)^-1ᵖ =>
      apply whisker001, apply whisker021,
      apply move201, refine _ @1p !eq_hconcat_hdeg_square^-1,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine ap (hconcat_eq _) !ap_inv @p1 _ @2p (natural_square_eq2 _ !functor_gluer2)^-1ᵖ =>
      apply whisker021,
      refine _ @1p ap hdeg_square (eq_of_square ((ap_pp _ _ _)stant_compose^-1ʰ) @ (concat_1p _))^-1,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine _ @2p !rec_eq_gluer^-1, apply whisker021,
      apply move221, refine _ @1p !hdeg_square_hconcat_eq^-1,
      refine _ @1p ap hdeg_square (eq_bot_of_square (transpose !ap02_constant)),
      exact rfl2 end end },
Defined.

Definition smash_functor_pcompose_pconst3 (f' : C ->* E) (f : A ->* C) (g : B ->* D) :
    phsquare (smash_functor_pcompose f' f (pconst D F) g)
             (smash_functor_pconst_right (f' o* f))
             (smash_functor_phomotopy (reflexivity _) (pconst_pcompose g))
             (pwhisker_right (f ∧-> g) (smash_functor_pconst_right f') @*
               pconst_pcompose (f ∧-> g)) :=
Proof.
    induction A with A a₀, induction B with B b₀,
    induction E with E e₀, induction C with C c₀, induction F with F x₀, induction D with D d₀,
    induction f' with f' f'₀, induction f with f f₀, induction g with g g₀,
    esimp at *, induction f'₀, induction f₀, induction g₀,
    refine !smash_functor_phomotopy_refl @ph** _ => refine _ @ !refl_trans^-1,
    fapply phomotopy_eq,
    { intro x, refine eq_of_square (smash_functor_pcompose_pconst3_homotopy a₀ b₀ x₀ f' f g x) } =>
    { refine whisker_right _ (!whisker_right_idp @ !eq_of_square_hrfl) @ _,
      have H : forall {A : Type} {a a' : A} (p : a = a'),
               idp_con (p @ p^-1) @ con.right_inv p = idp @
               whisker_left idp (idp @ (idp @ proof whisker_right idp (idp_con (p @ p^-1ᵖ))^-1ᵖ qed @
                 whisker_left idp (con.right_inv p))), by intros; induction p; reflexivity,
      rexact H (gluel (f' (f a₀))) }
Defined.

  (* a version where the left maps are identities *)
Definition smash_functor_pcompose_pconst3_pid (g : B ->* D) :
    phsquare (smash_functor_pid_pcompose A (pconst D F) g)
             (smash_functor_pconst_right (pid A))
             (smash_functor_phomotopy (reflexivity _) (pconst_pcompose g))
             (pwhisker_right (pid A ∧-> g) (smash_functor_pconst_right (pid A)) @*
               pconst_pcompose (pid A ∧-> g)) :=
  (!smash_functor_phomotopy_refl ◾** idp @ !refl_trans) @pv**
  smash_functor_pcompose_pconst3 (pid A) (pid A) g

  (* Using these lemmas we show that smash_functor_right is natural in all arguments *)
Definition smash_functor_right_natural_right (A B : pType) (f : C ->* C') :
    psquare (smash_functor_right A B C) (smash_functor_right A B C')
            (ppcompose_left f) (ppcompose_left (pid A ∧-> f)) :=
Proof.
    refine _^-1*,
    fapply phomotopy_mk_ppMap,
    { exact smash_functor_pid_pcompose A f } =>
    { refine idp ◾** (!phomotopy_path_con @ (ap phomotopy_path !pcompose_left_path_pforall @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy) @ _ ,
      refine _ @ (!phomotopy_path_con @ (ap phomotopy_path !smash_functor_path_pforall @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy)^-1,
      apply smash_functor_pcompose_pconst4_pid }
Defined.

Definition smash_functor_right_natural_middle (A C : pType) (f : B' ->* B) :
    psquare (smash_functor_right A B C) (smash_functor_right A B' C)
            (ppcompose_right f) (ppcompose_right (pid A ∧-> f)) :=
Proof.
    refine _^-1*,
    fapply phomotopy_mk_ppMap,
    { intro g, exact smash_functor_pid_pcompose A g f } =>
    { refine idp ◾** (!phomotopy_path_con @ (ap phomotopy_path !pcompose_right_path_pforall @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy) @ _ ,
      refine _ @ (!phomotopy_path_con @ (ap phomotopy_path !smash_functor_path_pforall @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy)^-1,
      apply smash_functor_pcompose_pconst3_pid }
Defined.

Definition smash_functor_right_natural_left (B C : pType) (f : A ->* A') :
    psquare (smash_functor_right A B C) (ppcompose_right (f ∧-> (pid B)))
            (smash_functor_right A' B C) (ppcompose_left (f ∧-> (pid C))) :=
Proof.
    refine _^-1*,
    fapply phomotopy_mk_ppMap,
    { intro g, exact smash_functor_psquare proof (reflexivity _) qed proof (reflexivity _) qed } =>
    { esimp,
      refine idp ◾** (!phomotopy_path_con @ (ap phomotopy_path !pcompose_left_path_pforall @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy) @ _ ,
      refine _ @ (!phomotopy_path_con @ (ap phomotopy_path !pcompose_right_path_pforall @
        !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy)^-1,
      apply eq_of_phsquare,
      refine (phmove_bot_of_left _ !smash_functor_pcompose_pconst3^-1ʰ**) @h**
        (!smash_functor_phomotopy_refl @pv** !phhrfl) @h** !smash_functor_pcompose_pconst4 @vp** _ =>
      refine !trans_assoc @ !trans_assoc @ idp ◾** _ @ !trans_refl,
      refine idp ◾** !refl_trans @ !trans_left_inv }
Defined.

  (* A ∧ B <~>* pcofiber (pprod_of_wedge A B) *)

  variables (A B)
  open pushout

Definition smash_equiv_cofiber : smash A B <~> cofiber (@prod_of_wedge A B) :=
Proof.
    unfold [smash, cofiber, smash'], symmetry,
    fapply pushout_vcompose_equiv wedge_of_sum,
    { symmetry, refine equiv_unit_of_is_contr _ _, apply is_contr_pushout_wedge_of_sum },
    { intro x, reflexivity },
    { apply prod_of_wedge_of_sum }
Defined.

Definition smash_punit_pequiv : smash A punit <~>* punit :=
Proof.
    apply pequiv_punit_of_is_contr,
    apply is_contr.mk (smash.mk (point _) ⋆), intro x,
    induction x,
    { induction b, exact gluel' (point _) a },
    { exact gluel (point _) },
    { exact gluer (point _) },
    { apply eq_pathover_constant_left_id_right, apply square_of_eq_top,
      exact whisker_right _ (concat_1p _)^-1 },
    { apply eq_pathover_constant_left_id_right, induction b,
      refine (con_pV _) @pv _, exact square_of_eq idp },
Defined.

Definition pprod_of_wedge : wedge A B ->* A \** B :=
Proof.
    fconstructor,
    { exact prod_of_wedge },
    { reflexivity }
Defined.

Definition smash_pequiv_pcofiber : smash A B <~>* pcofiber (pprod_of_wedge A B) :=
Proof.
    apply pequiv_of_equiv (smash_equiv_cofiber A B),
    exact cofiber.glue pt
Defined.

  variables {A B}

  (* commutativity *)

Definition smash_flip' (x : smash A B) : smash B A :=
Proof.
    induction x,
    { exact smash.mk b a },
    { exact auxr },
    { exact auxl },
    { exact gluer a },
    { exact gluel b }
Defined.

Definition smash_flip_smash_flip' (x : smash A B) : smash_flip' (smash_flip' x) = x :=
Proof.
    induction x,
    { reflexivity },
    { reflexivity },
    { reflexivity },
    { apply eq_pathover_id_right,
      refine ap_compose smash_flip' _ _ @ ap02 _ !elim_gluel @ !elim_gluer @ph _,
      apply hrfl },
    { apply eq_pathover_id_right,
      refine ap_compose smash_flip' _ _ @ ap02 _ !elim_gluer @ !elim_gluel @ph _,
      apply hrfl }
Defined.

  variables (A B)

Definition smash_flip : smash A B ->* smash B A :=
  Build_pMap smash_flip' idp

Definition smash_flip_smash_flip :
    smash_flip B A o* smash_flip A B ==* pid (A ∧ B) :=
  Build_pHomotopy smash_flip_smash_flip' idp

Definition smash_comm : smash A B <~>* smash B A :=
Proof.
    apply pequiv.MK, do 2 apply smash_flip_smash_flip
Defined.

  variables {A B}
Definition smash_flip_smash_functor' (f : A ->* C) (g : B ->* D) : hsquare
    smash_flip' smash_flip' (smash_functor' f g) (smash_functor' g f) :=
Proof.
    intro x, induction x,
    { reflexivity },
    { reflexivity },
    { reflexivity },
    { apply eq_pathover,
      refine ap_compose (smash_functor' _ _)  _ _ @ ap02 _ !elim_gluel @ !functor_gluer @ph _
        @hp (ap_compose smash_flip' _ _ @ ap02 _ !functor_gluel)^-1ᵖ =>
      refine _ @hp ((ap_pp _ _ _) @ !ap_compose' ◾ !elim_gluel)^-1, exact hrfl },
    { apply eq_pathover,
      refine ap_compose (smash_functor' _ _)  _ _ @ ap02 _ !elim_gluer @ !functor_gluel @ph _
        @hp (ap_compose smash_flip' _ _ @ ap02 _ !functor_gluer)^-1ᵖ =>
      refine _ @hp ((ap_pp _ _ _) @ !ap_compose' ◾ !elim_gluer)^-1, exact hrfl },
Defined.

Definition smash_flip_smash_functor (f : A ->* C) (g : B ->* D) :
    psquare (smash_flip A B) (smash_flip C D) (f ∧-> g) (g ∧-> f) :=
Proof.
    apply Build_pHomotopy (smash_flip_smash_functor' f g) => refine (concat_1p _) @ _ @ (concat_1p _)^-1,
    refine !ap_ap011 @ _, apply ap011_flip,
Defined.

Defined. smash
