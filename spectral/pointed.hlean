(* equalities between pointed homotopies and other facts about pointed types/functions/homotopies *)


import types.pointed2 .move_to_lib

open pointed eq equiv function is_equiv unit is_trunc trunc nat algebra sigma group lift option

namespace pointed

Definition phomotopy_mk_eq {A B : pType} {f g : A ->* B} {h k : f == g}
  {h₀ : h (point _) @ point_eq g = point_eq f} {k₀ : k (point _) @ point_eq g = point_eq f} (p : h == k)
  (q : whisker_right (point_eq g) (p (point _)) @ k₀ = h₀) : Build_pHomotopy h h₀ = Build_pHomotopy k k₀.
  phomotopy_eq p (idp ◾ to_right_inv !eq_con_inv_equiv_con_eq _ @
  q @ (to_right_inv !eq_con_inv_equiv_con_eq _)^-1)


  section phsquare
  (*
  Squares of pointed homotopies
  *)

  variables {A : pType} {P : A -> Type} {p₀ : P (point _)}
  {f f' f₀₀ f₂₀ f₄₀ f₀₂ f₂₂ f₄₂ f₀₄ f₂₄ f₄₄ : ppi P p₀}
  {p₁₀ : f₀₀ ==* f₂₀} {p₃₀ : f₂₀ ==* f₄₀}
  {p₀₁ : f₀₀ ==* f₀₂} {p₂₁ : f₂₀ ==* f₂₂} {p₄₁ : f₄₀ ==* f₄₂}
  {p₁₂ : f₀₂ ==* f₂₂} {p₃₂ : f₂₂ ==* f₄₂}
  {p₀₃ : f₀₂ ==* f₀₄} {p₂₃ : f₂₂ ==* f₂₄} {p₄₃ : f₄₂ ==* f₄₄}
  {p₁₄ : f₀₄ ==* f₂₄} {p₃₄ : f₂₄ ==* f₄₄}

Definition phtranspose (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : phsquare p₀₁ p₂₁ p₁₀ p₁₂.
  p^-1

Definition eq_top_of_phsquare (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : p₁₀ = p₀₁ @* p₁₂ @* p₂₁^-1*.
  eq_trans_symm_of_trans_eq p

Definition eq_bot_of_phsquare (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : p₁₂ = p₀₁^-1* @* p₁₀ @* p₂₁.
  eq_symm_trans_of_trans_eq p^-1 @ !trans_assoc^-1

Definition eq_left_of_phsquare (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : p₀₁ = p₁₀ @* p₂₁ @* p₁₂^-1*.
  eq_top_of_phsquare (phtranspose p)

Definition eq_right_of_phsquare (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : p₂₁ = p₁₀^-1* @* p₀₁ @* p₁₂.
  eq_bot_of_phsquare (phtranspose p)

Defined. phsquare







  (* todo: make type argument explicit in ppcompose_left and ppcompose_left_* *)
  (* todo: delete papply_pcompose *)
  (* todo: pmap_pbool_equiv is a special case of ppMap_pbool_pequiv. *)

Definition ppcompose_left_pid (A B : pType) : ppcompose_left (pid B) ==* pid (ppMap A B).
  phomotopy_mk_ppMap (fun f => pid_pcompose f) (!trans_refl @ !phomotopy_path_of_phomotopy^-1)

Definition ppcompose_right_pid (A B : pType) : ppcompose_right (pid A) ==* pid (ppMap A B).
  phomotopy_mk_ppMap (fun f => pcompose_pid f) (!trans_refl @ !phomotopy_path_of_phomotopy^-1)

  section
  variables {A A' : pType} {P : A -> Type} {P' : A' -> Type} {p₀ : P (point _)} {p₀' : P' (point _)} {k l : ppi P p₀}
Definition phomotopy_path_inv (p : k = l) :
  phomotopy_path p^-1 = (phomotopy_path p)^-1*.
Proof. induction p, exact !refl_symm^-1 end

  (* todo: replace regular pap *)
Definition pap' (f : ppi P p₀ -> ppi P' p₀') (p : k ==* l) : f k ==* f l.
  by induction p using phomotopy_rec_idp; reflexivity

Definition phomotopy_path_ap (f : ppi P p₀ -> ppi P' p₀') (p : k = l) :
  phomotopy_path (ap f p) = pap' f (phomotopy_path p).
Proof. induction p, exact !phomotopy_rec_idp_refl^-1 end
Defined.

  (* remove some duplicates: loop_ppMap_commute, loop_ppMap_pequiv, loop_ppMap_pequiv', pfunext *)













  (*
  Do we want to use a structure of homotopies between pointed homotopies? Or are equalities fine?
  If we set up things more generally, we could define this as
  "pointed homotopies between the dependent pointed maps p and q"
  *)
  structure phomotopy2 {A B : pType} {f g : A ->* B} (p q : f ==* g) : Type.
  (homotopy_eq : p == q)
  (homotopy_pt_eq : whisker_right (point_eq g) (homotopy_eq (point _)) @ point_htpy q =
  point_htpy p)

  (* this sets it up more generally, for illustrative purposes *)
  structure ppi' (A : pType) (P : A -> Type) (p : P (point _)).
  (to_fun : forall , P a)
  (resp_pt : to_fun (Point A) = p)
  attribute ppi'.to_fun [coercion]
Definition phomotopy' {A : pType} {P : A -> Type} {x : P (point _)} (f g : ppi' A P x) : Type.
  ppi' A (fun a => f a = g a) (ppi'.resp_pt f @ (ppi'.resp_pt g)^-1)
Definition phomotopy2' {A : pType} {P : A -> Type} {x : P (point _)} {f g : ppi' A P x}
  (p q : phomotopy' f g) : Type.
  phomotopy' p q




Definition pconst_pcompose_phomotopy {A B C : pType} {f f' : A ->* B} (p : f ==* f') :
  pwhisker_left (pconst B C) p @* pconst_pcompose f' = pconst_pcompose f.
Proof.
  fapply phomotopy_eq,
  { intro a, apply ap_constant },
  { induction p using phomotopy_rec_idp, induction B with B b₀, induction f with f f₀,
  esimp at *, induction f₀, reflexivity }
Defined.

(* Homotopy between a function and its eta expansion *)

Definition papply_point (A B : pType) : papply B (point _) ==* pconst (ppMap A B) B.
  Build_pHomotopy (fun f => point_eq f) idp

Definition pmap_swap_map {A B C : pType} (f : A ->* ppMap B C) :
  ppMap B (ppMap A C).
Proof.
  fapply Build_pMap,
  { intro b, exact papply C b o* f },
  { apply path_pforall, exact pwhisker_right f (papply_point B C) @* !pconst_pcompose }
Defined.

Definition pmap_swap_map_pconst (A B C : pType) :
  pmap_swap_map (pconst A (ppMap B C)) ==* pconst B (ppMap A C).
Proof.
  fapply phomotopy_mk_ppMap,
  { intro b, reflexivity },
  { refine !refl_trans @ !phomotopy_path_of_phomotopy^-1 }
Defined.

Definition papply_pmap_swap_map {A B C : pType} (f : A ->* ppMap B C) (a : A) :
  papply C a o* pmap_swap_map f ==* f a.
Proof.
  fapply Build_pHomotopy,
  { intro b, reflexivity },
  { exact (concat_1p _) @ !ap_path_pforall^-1 }
Defined.

Definition pmap_swap_map_pmap_swap_map {A B C : pType} (f : A ->* ppMap B C) :
  pmap_swap_map (pmap_swap_map f) ==* f.
Proof.
  fapply phomotopy_mk_ppMap,
  { exact papply_pmap_swap_map f },
  { refine _ @ !phomotopy_path_of_phomotopy^-1,
  fapply phomotopy_mk_eq, intro b, exact (concat_1p _),
  refine !whisker_right_idp ◾ ((concat_1p _) ◾ idp) @ _ @ (concat_1p _)^-1 ◾ idp,
  symmetry, exact sorry }
Defined.

Definition pmap_swap (A B C : pType) : ppMap A (ppMap B C) ->* ppMap B (ppMap A C).
Proof.
  fapply Build_pMap,
  { exact pmap_swap_map },
  { exact path_pforall (pmap_swap_map_pconst A B C) }
Defined.

Definition pmap_swap_pequiv (A B C : pType) :
  ppMap A (ppMap B C) <~>* ppMap B (ppMap A C).
Proof.
  fapply pequiv_of_pmap,
  { exact pmap_swap A B C },
  fapply adjointify,
  { exact pmap_swap B A C },
  { intro f, apply path_pforall, exact pmap_swap_map_pmap_swap_map f },
  { intro f, apply path_pforall, exact pmap_swap_map_pmap_swap_map f }
Defined.

Definition pnatural_square2 {A B : Type} (X : B -> pType) (Y : B -> pType) {f g : A -> B}
  (h : forall a, X (f a) ->* Y (g a)) {a a' : A} (p : a = a') :
  h a' o* ptransport X (ap f p) ==* ptransport Y (ap g p) o* h a.
  by induction p; exact !pcompose_pid @* !pid_pcompose^-1*

Definition ptransport_ap {A B : Type} (X : B -> pType) (f : A -> B) {a a' : A} (p : a = a') :
  ptransport X (ap f p) ==* ptransport (X o f) p.
  by induction p; reflexivity

Definition ptransport_constant (A : Type) (B : pType) {a a' : A} (p : a = a') :
  ptransport (fun (a : A) => B) p ==* pid B.
  by induction p; reflexivity

Definition ptransport_natural {A : Type} (X : A -> pType) (Y : A -> pType)
  (h : forall a, X a ->* Y a) {a a' : A} (p : a = a') :
  h a' o* ptransport X p ==* ptransport Y p o* h a.
  by induction p; exact !pcompose_pid @* !pid_pcompose^-1*

  section psquare
  variables {A A' A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : pType}
  {f₁₀ f₁₀' : A₀₀ ->* A₂₀} {f₃₀ : A₂₀ ->* A₄₀}
  {f₀₁ f₀₁' : A₀₀ ->* A₀₂} {f₂₁ f₂₁' : A₂₀ ->* A₂₂} {f₄₁ f₄₁' : A₄₀ ->* A₄₂}
  {f₁₂ f₁₂' : A₀₂ ->* A₂₂} {f₃₂ : A₂₂ ->* A₄₂}
  {f₀₃ : A₀₂ ->* A₀₄} {f₂₃ : A₂₂ ->* A₂₄} {f₄₃ : A₄₂ ->* A₄₄}
  {f₁₄ f₁₄' : A₀₄ ->* A₂₄} {f₃₄ : A₂₄ ->* A₄₄}

Definition pvconst_square_pcompose (f₃₀ : A₂₀ ->* A₄₀) (f₁₀ : A₀₀ ->* A₂₀)
  (f₃₂ : A₂₂ ->* A₄₂) (f₁₂ : A₀₂ ->* A₂₂) :
  pvconst_square (f₃₀ o* f₁₀) (f₃₂ o* f₁₂) = pvconst_square f₁₀ f₁₂ @h* pvconst_square f₃₀ f₃₂.
Proof.
  refine eq_right_of_phsquare !passoc_pconst_left ◾** !passoc_pconst_right^-1⁻²** @ idp ◾**
  (!trans_symm @ !trans_symm ◾** idp) @ !trans_assoc^-1 @ _ ◾** idp,
  refine !trans_assoc^-1 @ _ ◾** !pwhisker_left_symm^-1 @ !trans_assoc @
  idp ◾** !pwhisker_left_trans^-1,
  apply trans_symm_eq_of_eq_trans,
  refine _ @ idp ◾** !passoc_pconst_middle^-1 @ !trans_assoc^-1 @ !trans_assoc^-1,
  refine _ ◾** idp @ !trans_assoc,
  refine idp ◾** _ @ !trans_assoc^-1,
  refine ap (pwhisker_right f₁₀) _ @ !pwhisker_right_trans,
  refine !trans_refl^-1 @ idp ◾** !trans_left_inv^-1 @ !trans_assoc^-1,
Defined.

Definition phconst_square_pcompose (f₀₃ : A₀₂ ->* A₀₄) (f₁₀ : A₀₀ ->* A₂₀)
  (f₂₃ : A₂₂ ->* A₂₄) (f₂₁ : A₂₀ ->* A₂₂) :
  phconst_square (f₀₃ o* f₀₁) (f₂₃ o* f₁₂) = phconst_square f₀₁ f₁₂ @v* phconst_square f₀₃ f₂₃.
  sorry

Definition rfl_phomotopy_hconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : (reflexivity _) @ph* p = p.
  idp ◾** (ap (pwhisker_left f₁₂) !refl_symm @ !pwhisker_left_refl) @ !trans_refl

Definition hconcat_phomotopy_rfl (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : p @hp* (reflexivity _) = p.
  !pwhisker_right_refl ◾** idp @ !refl_trans

Definition rfl_phomotopy_vconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : (reflexivity _) @pv* p = p.
  !pwhisker_left_refl ◾** idp @ !refl_trans

Definition vconcat_phomotopy_rfl (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : p @vp* (reflexivity _) = p.
  idp ◾** (ap (pwhisker_right f₀₁) !refl_symm @ !pwhisker_right_refl) @ !trans_refl

Definition phomotopy_hconcat_phconcat (p : f₀₁' ==* f₀₁) (q : psquare f₁₀ f₁₂ f₀₁ f₂₁)
  (r : psquare f₃₀ f₃₂ f₂₁ f₄₁) : (p @ph* q) @h* r = p @ph* (q @h* r).
Proof.
  induction p using phomotopy_rec_idp,
  exact !refl_phomotopy_hconcat ◾h* idp @ !refl_phomotopy_hconcat^-1
Defined.

Definition phconcat_hconcat_phomotopy (p : psquare f₁₀ f₁₂ f₀₁ f₂₁)
  (q : psquare f₃₀ f₃₂ f₂₁ f₄₁) (r : f₄₁' ==* f₄₁) : (p @h* q) @hp* r = p @h* (q @hp* r).
Proof.
  induction r using phomotopy_rec_idp,
  exact !hconcat_phomotopy_rfl @ idp ◾h* !hconcat_phomotopy_rfl^-1
Defined.

Definition phomotopy_hconcat_phomotopy (p : f₀₁' ==* f₀₁) (q : psquare f₁₀ f₁₂ f₀₁ f₂₁)
  (r : f₂₁' ==* f₂₁) : (p @ph* q) @hp* r = p @ph* (q @hp* r).
Proof.
  induction r using phomotopy_rec_idp,
  exact !hconcat_phomotopy_rfl @ idp ◾ph* !hconcat_phomotopy_rfl^-1
Defined.

Definition hconcat_phomotopy_phconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁)
  (q : f₂₁' ==* f₂₁) (r : psquare f₃₀ f₃₂ f₂₁' f₄₁) : (p @hp* q) @h* r = p @h* (q^-1* @ph* r).
Proof.
  induction q using phomotopy_rec_idp,
  exact !hconcat_phomotopy_rfl ◾h* idp @ idp ◾h* (!refl_symm ◾ph* idp @ !refl_phomotopy_hconcat)^-1
Defined.

Definition phconcat_phomotopy_hconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁)
  (q : f₂₁ ==* f₂₁') (r : psquare f₃₀ f₃₂ f₂₁' f₄₁) : p @h* (q @ph* r) = (p @hp* q^-1*) @h* r.
Proof.
  induction q using phomotopy_rec_idp,
  exact idp ◾h* !refl_phomotopy_hconcat @ (idp ◾hp* !refl_symm @ !hconcat_phomotopy_rfl)^-1 ◾h* idp
Defined.

Definition hconcat_phomotopy_hconcat_cancel (p : psquare f₁₀ f₁₂ f₀₁ f₂₁)
  (q : f₂₁' ==* f₂₁) (r : psquare f₃₀ f₃₂ f₂₁ f₄₁) : (p @hp* q) @h* (q @ph* r) = p @h* r.
Proof.
  induction q using phomotopy_rec_idp,
  exact !hconcat_phomotopy_rfl ◾h* !refl_phomotopy_hconcat
Defined.

Definition phomotopy_hconcat_phinverse {f₁₀ : A₀₀ <~>* A₂₀} {f₁₂ : A₀₂ <~>* A₂₂}
  (p : f₀₁' ==* f₀₁) (q : psquare f₁₀ f₁₂ f₀₁ f₂₁) : (p @ph* q)^-1ʰ* = q^-1ʰ* @hp* p.
Proof.
  induction p using phomotopy_rec_idp,
  exact !refl_phomotopy_hconcat⁻²ʰ* @ !hconcat_phomotopy_rfl^-1
Defined.

Definition hconcat_phomotopy_phinverse {f₁₀ : A₀₀ <~>* A₂₀} {f₁₂ : A₀₂ <~>* A₂₂}
  (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : f₂₁' ==* f₂₁) : (p @hp* q)^-1ʰ* = q @ph* p^-1ʰ*.
Proof.
  induction q using phomotopy_rec_idp,
  exact !hconcat_phomotopy_rfl⁻²ʰ* @ !refl_phomotopy_hconcat^-1
Defined.

Definition pvconst_square_phinverse (f₁₀ : A₀₀ <~>* A₂₀) (f₁₂ : A₀₂ <~>* A₂₂) :
  (pvconst_square f₁₀ f₁₂)^-1ʰ* = pvconst_square f₁₀^-1ᵉ* f₁₂^-1ᵉ*.
Proof.
  exact sorry
Defined.

Definition ppcompose_left_phomotopy_hconcat (A : pType) (p : f₀₁' ==* f₀₁)
  (q : psquare f₁₀ f₁₂ f₀₁ f₂₁) : ppcompose_left_psquare (p @ph* q) =
  @ppcompose_left_phomotopy A _ _ _ _ p @ph* ppcompose_left_psquare q.
  sorry --used

Definition ppcompose_left_hconcat_phomotopy (A : pType) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁)
  (q : f₂₁' ==* f₂₁) : ppcompose_left_psquare (p @hp* q) =
  ppcompose_left_psquare p @hp* @ppcompose_left_phomotopy A _ _ _ _ q.
  sorry

Definition ppcompose_left_pvconst_square (A : pType) (f₁₀ : A₀₀ ->* A₂₀) (f₁₂ : A₀₂ ->* A₂₂) :
  ppcompose_left_psquare (pvconst_square f₁₀ f₁₂) =
  !ppcompose_left_pconst @ph* pvconst_square (ppcompose_left f₁₀) (@ppcompose_left A _ _ f₁₂) @hp*
  !ppcompose_left_pconst.
  sorry

Defined. psquare

Definition ap1_pequiv_ap {A : Type} (B : A -> pType) {a a' : A} (p : a = a') :
  Ω-> (pequiv_ap B p) ==* pequiv_ap (loops o B) p.
Proof. induction p, apply ap1_pid end

Definition pequiv_ap_natural {A : Type} (B C : A -> pType) {a a' : A} (p : a = a')
  (f : forall a, B a ->* C a) :
  psquare (pequiv_ap B p) (pequiv_ap C p) (f a) (f a').
Proof. induction p, exact phrfl end

Definition is_contr_loop (A : pType) [is_set A] : is_contr (loops A).
  is_contr.mk idp (fun a => !is_prop.elim)

Definition is_contr_loop_of_is_contr {A : pType} (H : is_contr A) : is_contr (loops A).
  is_contr_loop A

Definition is_contr_punit [instance] : is_contr punit.
  is_contr_unit

Definition pequiv_of_is_contr (A B : pType) (HA : is_contr A) (HB : is_contr B) : A <~>* B.
  pequiv_punit_of_is_contr A _ @e* (pequiv_punit_of_is_contr B _)^-1ᵉ*

Definition loop_pequiv_punit_of_is_set (X : pType) [is_set X] : loops X <~>* punit.
  pequiv_punit_of_is_contr _ (is_contr_loop X)

Definition loop_punit : loops punit <~>* punit.
  loop_pequiv_punit_of_is_set punit

Definition add_point_functor' {A B : Type} (e : A -> B) (a : A₊) : B₊.
Proof. induction a with a, exact none, exact some (e a) end

Definition add_point_functor {A B : Type} (e : A -> B) : A₊ ->* B₊.
  Build_pMap (add_point_functor' e) idp

Definition add_point_functor_compose {A B C : Type} (f : B -> C) (e : A -> B) :
  add_point_functor (f o e) ==* add_point_functor f o* add_point_functor e.
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x: reflexivity },
  reflexivity
Defined.

Definition add_point_functor_id (A : Type) :
  add_point_functor id ==* pid A₊.
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x: reflexivity },
  reflexivity
Defined.

Definition add_point_functor_phomotopy {A B : Type} {e e' : A -> B} (p : e == e') :
  add_point_functor e ==* add_point_functor e'.
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x with a, reflexivity, exact ap some (p a) },
  reflexivity
Defined.

Definition add_point_pequiv {A B : Type} (e : A <~> B) : A₊ <~>* B₊.
  pequiv.MK (add_point_functor e) (add_point_functor e^-1ᵉ)
  abstract !add_point_functor_compose^-1* @* add_point_functor_phomotopy (left_inv e) @*
  !add_point_functor_id end
  abstract !add_point_functor_compose^-1* @* add_point_functor_phomotopy (right_inv e) @*
  !add_point_functor_id end

Definition add_point_over {A : Type} (B : A -> pType) : A₊ -> pType
  | (some a) . B a
  | none     . plift punit

Definition add_point_over_pequiv {A : Type} {B B' : A -> pType} (e : forall a, B a <~>* B' a) :
  forall (a : A₊), add_point_over B a <~>* add_point_over B' a
  | (some a) . e a
  | none     . pequiv.rfl

Definition phomotopy_group_plift_punit.{u} (n : ℕ) [H : is_at_least_two n] :
  forall ag[n] (plift.{0 u} punit) <~>g trivial_ab_group_lift.{u}.
Proof.
  induction H with n,
  have H : 0 <[ℕ] n+2, from !zero_lt_succ,
  have is_set unit, from _,
  have is_trunc (trunc_index.of_nat 0) punit, from this,
  exact isomorphism_of_is_contr (@trivial_homotopy_group_of_is_trunc _ _ _ !is_trunc_lift H)
  !is_trunc_lift
Defined.

Definition pmap_of_map_pt {A : pType} {B : Type} (f : A -> B) :
  A ->* pointed.MK B (f (point _)).
  Build_pMap f idp

Definition papply_natural_right {A B B' : pType} (f : B ->* B') (a : A) :
  psquare (papply B a) (papply B' a) (ppcompose_left f) f.
Proof.
  fapply Build_pHomotopy,
  { intro g, reflexivity },
  { refine (concat_1p _) @ !ap_path_pforall @ (concat_1p _)^-1 }
Defined.


(*
whisker_right
  (ap (fun f => pppi.to_fun f a)
  (path_pforall (pcompose_pconst (pconst B B'))))
  (idp_con
  (ap (fun y => pppi.to_fun y a)
  (path_pforall
  (pconst_pcompose (ppi_const (fun a => B))))^-1) @ ap_inv
  (fun y => pppi.to_fun y a)
  (path_pforall
  (pconst_pcompose (ppi_const (fun a => B)))) @ inverse2
  (ap_path_pforall , B)))
  a))^-1 @ (con.assoc
  (ppi.to_fun (pvconst_square (papply B a) (papply B' a))
  (ppi_const (fun a => B)))
  (ap (fun f => pppi.to_fun f a)
  (path_pforall , B))))^-1)
  (ap (fun f => pppi.to_fun f a)
  (path_pforall
  (pcompose_pconst (pconst B B')))) @ whisker_left
  (ppi.to_fun (pvconst_square (papply B a) (papply B' a))
  (ppi_const (fun a => B)))
  (con_eq_of_eq_con_inv
  (eq_con_inv_of_con_eq
  (pwhisker_left_1 B' (ppMap A B) (ppMap A B') (papply B' a)
  (pconst (ppMap A B) (ppMap A B'))
  (ppcompose_left (pconst B B'))
  (ppcompose_left_pconst A B B')^-1*))) @ point_eq
  (pvconst_square (papply B a) (papply B' a))) = idp_con
  (ap (fun f => pppi.to_fun f a)
  (path_pforall
  (pcompose_pconst (pconst B B')))) @ ap_path_pforall
  (pcompose_pconst (pconst B B'))
  a
*)



Definition papply_natural_right_pconst {A : pType} (B B' : pType) (a : A) :
  papply_natural_right (pconst B B') a = !ppcompose_left_pconst @ph* !pvconst_square.
Proof.
  fapply phomotopy_mk_eq,
  { intro g, symmetry, refine (concat_1p _) @ !ap_inv @ !ap_path_pforall⁻² },
  {

  esimp [pvconst_square],
  --esimp [inv_con_eq_of_eq_con, pwhisker_left_1]
  exact sorry }
Defined.


  (* TODO: computation rule *)
  open pi
Definition fiberwise_pointed_map_rec {A : Type} {B : A -> pType}
  (P : forall (C : A -> pType) (g : forall a, B a ->* C a), Type)
  (H : forall (C : A -> Type) (g : forall a, B a -> C a), P _ (fun a => pmap_of_map_pt (g a))) :
  forall (C : A -> pType) (g : forall a, B a ->* C a), P C g.
Proof.
  refine equiv_rect (!sigma_pi_equiv_pi_sigma @e
  arrow_equiv_arrow_right A !pType.sigma_char^-1ᵉ) _ _,
  intro R, cases R with R r₀,
  refine equiv_rect (!sigma_pi_equiv_pi_sigma @e
  pi_equiv_pi_right (fun a => !pmap.sigma_char^-1ᵉ)) _ _,
  intro g, cases g with g g₀, esimp at (g, g₀),
  revert g₀, change (forall , g a (Point (B a))) == r₀), _),
  refine homotopy.rec_idp _ _, esimp,
  apply H
Defined.

Definition ap1_gen_idp_eq {A B : Type} (f : A -> B) {a : A} (q : f a = f a) (r : q = idp) :
  ap1_gen_idp f q = ap (fun x => ap1_gen f x x idp) r.
Proof. cases r, reflexivity end

Definition pointed_change_point (A : pType) {a : A} (p : a = (point _)) :
  pointed.MK A a <~>* A.
pequiv_of_eq_pt p @e* (pointed_eta_pequiv A)^-1ᵉ*

Definition change_path_psquare {A B : pType} (f : A ->* B)
  {a' : A} {b' : B} (p : a' = (point _)) (q : (point _) = b') :
  psquare (pointed_change_point _ p)
  (pointed_change_point _ q^-1)
  (Build_pMap f (ap f p @ point_eq f @ q)) f.
Proof.
  fapply Build_pHomotopy, exact homotopy.rfl,
  exact (concat_1p _) @ !ap_id ◾ !ap_id @ !con_inv_cancel_right @ whisker_right _ (ap02 f !ap_id^-1)
Defined.

Definition change_path_psquare_cod {A B : pType} (f : A ->* B) {b' : B} (p : (point _) = b') :
  f ==* pointed_change_point _ p^-1 o* Build_pMap f (point_eq f @ p).
Proof.
  fapply Build_pHomotopy, exact homotopy.rfl, exact (concat_1p _) @ !ap_id ◾ !ap_id @ !con_inv_cancel_right
Defined.

Definition change_path_psquare_cod' {A B : Type} (f : A -> B) (a : A) {b' : B} (p : f a = b') :
  pointed_change_point _ p o* pmap_of_map f a ==* Build_pMap f p.
Proof.
  fapply Build_pHomotopy, exact homotopy.rfl, refine whisker_left idp (ap_id p)^-1
Defined.

structure deloopable.{u} [class] (A : pType.{u}) : Type.{u+1}.
  (deloop : pType.{u})
  (deloop_pequiv : loops deloop <~>* A)

abbreviation deloop . deloopable.deloop
abbreviation deloop_pequiv . deloopable.deloop_pequiv

Definition deloopable_loop [instance] (A : pType) : deloopable (loops A).
deloopable.mk A pequiv.rfl

Definition deloopable_loopn [instance] [priority 500] (n : ℕ) [H : is_succ n] (A : pType) :
  deloopable (Ω[n] A).
by induction H with n; exact deloopable.mk (Ω[n] A) pequiv.rfl

Definition inf_group_of_deloopable (A : pType) [deloopable A] : inf_group A.
inf_group_equiv_closed (deloop_pequiv A) _

Definition InfGroup_of_deloopable (A : pType) [deloopable A] : InfGroup.
InfGroup.mk A (inf_group_of_deloopable A)

Definition deloop_isomorphism (A : pType) [deloopable A] :
  Ωg (deloop A) <~>∞g InfGroup_of_deloopable A.
InfGroup_equiv_closed_isomorphism (Ωg (deloop A)) (deloop_pequiv A)


Defined. pointed
