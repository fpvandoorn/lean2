(*
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

More results about pointed types.

Contains
- squares of pointed maps,
- equalities between pointed homotopies and
- squares between pointed homotopies
- pointed maps into and out of (ppMap A B), the pointed type of pointed maps from A to B
*)


import algebra.homotopy_group eq2

open pointed eq unit is_trunc trunc nat group is_equiv equiv sigma function bool

namespace pointed
  variables {A B C : pType} {P : A -> Type} {p₀ : P (point _)} {k k' l m n : ppi P p₀}

  section psquare
  (*
    Squares of pointed maps

    We treat expressions of the form
      psquare f g h k :≡ k o* f ==* g o* h
    as squares, where f is the top, g is the bottom, h is the left face and k is the right face.
    Then the following are operations on squares
  *)

  variables {A' A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : pType}
            {f₁₀ f₁₀' : A₀₀ ->* A₂₀} {f₃₀ : A₂₀ ->* A₄₀}
            {f₀₁ f₀₁' : A₀₀ ->* A₀₂} {f₂₁ f₂₁' : A₂₀ ->* A₂₂} {f₄₁ : A₄₀ ->* A₄₂}
            {f₁₂ f₁₂' : A₀₂ ->* A₂₂} {f₃₂ : A₂₂ ->* A₄₂}
            {f₀₃ : A₀₂ ->* A₀₄} {f₂₃ : A₂₂ ->* A₂₄} {f₄₃ : A₄₂ ->* A₄₄}
            {f₁₄ : A₀₄ ->* A₂₄} {f₃₄ : A₂₄ ->* A₄₄}

Definition psquare (f₁₀ : A₀₀ ->* A₂₀) (f₁₂ : A₀₂ ->* A₂₂)
                                 (f₀₁ : A₀₀ ->* A₀₂) (f₂₁ : A₂₀ ->* A₂₂) : Type.
  f₂₁ o* f₁₀ ==* f₁₂ o* f₀₁

Definition psquare_of_phomotopy (p : f₂₁ o* f₁₀ ==* f₁₂ o* f₀₁) : psquare f₁₀ f₁₂ f₀₁ f₂₁.
  p

Definition phomotopy_of_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : f₂₁ o* f₁₀ ==* f₁₂ o* f₀₁.
  p

Definition phdeg_square {f f' : A ->* A'} (p : f ==* f') : psquare !pid !pid f f'.
  !pcompose_pid @* p^-1* @* !pid_pcompose^-1*
Definition pvdeg_square {f f' : A ->* A'} (p : f ==* f') : psquare f f' !pid !pid.
  !pid_pcompose @* p @* !pcompose_pid^-1*

  variables (f₀₁ f₁₀)
Definition phrefl : psquare !pid !pid f₀₁ f₀₁ . phdeg_square (reflexivity _)
Definition pvrefl : psquare f₁₀ f₁₀ !pid !pid . pvdeg_square (reflexivity _)
  variables {f₀₁ f₁₀}
Definition phrfl : psquare !pid !pid f₀₁ f₀₁ . phrefl f₀₁
Definition pvrfl : psquare f₁₀ f₁₀ !pid !pid . pvrefl f₁₀

Definition phconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare f₃₀ f₃₂ f₂₁ f₄₁) :
    psquare (f₃₀ o* f₁₀) (f₃₂ o* f₁₂) f₀₁ f₄₁.
  !passoc^-1* @* pwhisker_right f₁₀ q @* !passoc @* pwhisker_left f₃₂ p @* !passoc^-1*

Definition pvconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare f₁₂ f₁₄ f₀₃ f₂₃) :
    psquare f₁₀ f₁₄ (f₀₃ o* f₀₁) (f₂₃ o* f₂₁).
  !passoc @* pwhisker_left _ p @* !passoc^-1* @* pwhisker_right _ q @* !passoc

Definition phinverse {f₁₀ : A₀₀ <~>* A₂₀} {f₁₂ : A₀₂ <~>* A₂₂} (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare f₁₀^-1ᵉ* f₁₂^-1ᵉ* f₂₁ f₀₁.
  !pid_pcompose^-1* @* pwhisker_right _ (pleft_inv f₁₂)^-1* @* !passoc @*
  pwhisker_left _
    (!passoc^-1* @* pwhisker_right _ p^-1* @* !passoc @* pwhisker_left _ !pright_inv @* !pcompose_pid)

Definition pvinverse {f₀₁ : A₀₀ <~>* A₀₂} {f₂₁ : A₂₀ <~>* A₂₂} (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare f₁₂ f₁₀ f₀₁^-1ᵉ* f₂₁^-1ᵉ*.
  (phinverse p^-1*)^-1*

Definition phomotopy_hconcat (q : f₀₁' ==* f₀₁) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare f₁₀ f₁₂ f₀₁' f₂₁.
  p @* pwhisker_left f₁₂ q^-1*

Definition hconcat_phomotopy (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : f₂₁' ==* f₂₁) :
    psquare f₁₀ f₁₂ f₀₁ f₂₁'.
  pwhisker_right f₁₀ q @* p

Definition phomotopy_vconcat (q : f₁₀' ==* f₁₀) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare f₁₀' f₁₂ f₀₁ f₂₁.
  pwhisker_left f₂₁ q @* p

Definition vconcat_phomotopy (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : f₁₂' ==* f₁₂) :
    psquare f₁₀ f₁₂' f₀₁ f₂₁.
  p @* pwhisker_right f₀₁ q^-1*

  infix ` @h* `:73 . phconcat
  infix ` @v* `:73 . pvconcat
  infixl ` @hp* `:72 . hconcat_phomotopy
  infixr ` @ph* `:72 . phomotopy_hconcat
  infixl ` @vp* `:72 . vconcat_phomotopy
  infixr ` @pv* `:72 . phomotopy_vconcat
  postfix `^-1ʰ*`:(max+1) . phinverse
  postfix `^-1ᵛ*`:(max+1) . pvinverse

Definition pwhisker_tl (f : A ->* A₀₀) (q : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (f₁₀ o* f) f₁₂ (f₀₁ o* f) f₂₁.
  !passoc^-1* @* pwhisker_right f q @* !passoc

Definition ap1_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (Ω-> f₁₀) (Ω-> f₁₂) (Ω-> f₀₁) (Ω-> f₂₁).
  !ap1_pcompose^-1* @* ap1_phomotopy p @* !ap1_pcompose

Definition apn_psquare (n : ℕ) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (Ω->[n] f₁₀) (Ω->[n] f₁₂) (Ω->[n] f₀₁) (Ω->[n] f₂₁).
  !apn_pcompose^-1* @* apn_phomotopy n p @* !apn_pcompose

Definition ptrunc_functor_psquare (n : ℕ₋₂) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (ptrunc_functor n f₁₀) (ptrunc_functor n f₁₂)
            (ptrunc_functor n f₀₁) (ptrunc_functor n f₂₁).
  !ptrunc_functor_pcompose^-1* @* ptrunc_functor_phomotopy n p @* !ptrunc_functor_pcompose

Definition homotopy_group_functor_psquare (n : ℕ) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
        psquare (forall ->[n] f₁₀) (forall ->[n] f₁₂) (forall ->[n] f₀₁) (forall ->[n] f₂₁).
  !homotopy_group_functor_compose^-1* @* homotopy_group_functor_phomotopy n p @*
  !homotopy_group_functor_compose

Definition homotopy_group_homomorphism_psquare (n : ℕ) [H : is_succ n]
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : hsquare (forall ->g[n] f₁₀) (forall ->g[n] f₁₂) (forall ->g[n] f₀₁) (forall ->g[n] f₂₁).
Proof.
    induction H with n, exact to_homotopy (ptrunc_functor_psquare 0 (apn_psquare (succ n) p))
Defined.

Defined. psquare

Definition punit_pmap_phomotopy {A : pType} (f : punit ->* A) :
    f ==* pconst punit A.
  !phomotopy_of_is_contr_dom

Definition punit_ppi (P : punit -> pType) (p₀ : P ⋆) : ppi P p₀.
Proof.
    fapply ppi.mk, intro u, induction u, exact p₀,
    reflexivity
Defined.

Definition punit_ppi_phomotopy {P : punit -> pType} {p₀ : P ⋆} (f : ppi P p₀) :
    f ==* punit_ppi P p₀.
  !phomotopy_of_is_contr_dom

Definition is_contr_punit_ppi (P : punit -> pType) (p₀ : P ⋆) : is_contr (ppi P p₀).
  is_contr.mk (punit_ppi P p₀) (fun f => path_pforall (punit_ppi_phomotopy f)^-1*)

Definition is_contr_punit_pmap (A : pType) : is_contr (punit ->* A).
  !is_contr_punit_ppi

  (*Definition phomotopy_eq_equiv (h₁ h₂ : k ==* l) : *)
  (*   (h₁ = h₂) <~> Σ(p : to_homotopy h₁ == to_homotopy h₂), *)
  (*     whisker_right (point_eq l) (p (point _)) @ point_htpy h₂ = point_htpy h₁ . *)
  (* begin *)
  (*   refine !ppi_eq_equiv @e !phomotopy.sigma_char @e sigma_equiv_sigma_right _, *)
  (*   intro p, *)
  (* end *)

  (* Short term TODO: generalize to dependent maps (use ppi_eq_equiv?)
     Long term TODO: use homotopies between pointed homotopies, not equalities
  *)

Definition phomotopy_eq_equiv {A B : pType} {f g : A ->* B} (h k : f ==* g) :
    (h = k) <~> Σ(p : to_homotopy h == to_homotopy k),
      whisker_right (point_eq g) (p (point _)) @ point_htpy k = point_htpy h.
  calc
    h = k <~> phomotopy.sigma_char _ _ h = phomotopy.sigma_char _ _ k
      : eq_equiv_fn_eq (phomotopy.sigma_char f g) h k
      ... <~> Σ(p : to_homotopy h = to_homotopy k),
              pathover (fun p => p (point _) @ point_eq g = point_eq f) (point_htpy h) p (point_htpy k)
      : sigma_eq_equiv _ _
      ... <~> Σ(p : to_homotopy h = to_homotopy k),
              point_htpy h = ap (fun q => q (point _) @ point_eq g) p @ point_htpy k
      : sigma_equiv_sigma_right (fun p => eq_pathover_equiv_Fl p (point_htpy h) (point_htpy k))
      ... <~> Σ(p : to_homotopy h = to_homotopy k),
              ap (fun q => q (point _) @ point_eq g) p @ point_htpy k = point_htpy h
      : sigma_equiv_sigma_right (fun p => eq_equiv_eq_symm _ _)
      ... <~> Σ(p : to_homotopy h = to_homotopy k),
      whisker_right (point_eq g) (apd10 p (point _)) @ point_htpy k = point_htpy h
      : sigma_equiv_sigma_right (fun p => equiv_eq_closed_left _ (whisker_right _ !whisker_right_ap^-1))
      ... <~> Σ(p : to_homotopy h == to_homotopy k),
      whisker_right (point_eq g) (p (point _)) @ point_htpy k = point_htpy h
      : sigma_equiv_sigma_left' eq_equiv_homotopy

Definition phomotopy_eq {A B : pType} {f g : A ->* B} {h k : f ==* g} (p : to_homotopy h == to_homotopy k)
    (q : whisker_right (point_eq g) (p (point _)) @ point_htpy k = point_htpy h) : h = k.
  to_inv (phomotopy_eq_equiv h k) ⟨p, q⟩

Definition phomotopy_eq' {A B : pType} {f g : A ->* B} {h k : f ==* g} (p : to_homotopy h == to_homotopy k)
    (q : square (point_htpy h) (point_htpy k) (whisker_right (point_eq g) (p (point _))) idp) : h = k.
  phomotopy_eq p (eq_of_square q)^-1

Definition trans_refl (p : k ==* l) : p @* (reflexivity _) = p.
Proof.
    induction A with A a₀,
    induction k with k k₀, induction l with l l₀, induction p with p p₀', esimp at * ⊢,
    induction l₀, induction p₀', reflexivity,
Defined.

Definition path_pforall_trans {X Y : pType} {f g h : X ->* Y} (p : f ==* g) (q : g ==* h) :
    path_pforall (p @* q) = path_pforall p @ path_pforall q.
Proof.
    induction p using phomotopy_rec_idp, induction q using phomotopy_rec_idp,
    exact ap path_pforall !trans_refl @ whisker_left _ !path_pforall_refl^-1
Defined.

Definition refl_trans (p : k ==* l) : (reflexivity _) @* p = p.
Proof.
    induction p using phomotopy_rec_idp,
    apply trans_refl
Defined.

Definition trans_assoc (p : k ==* l) (q : l ==* m) (r : m ==* n) : p @* q @* r = p @* (q @* r).
Proof.
    induction r using phomotopy_rec_idp,
    induction q using phomotopy_rec_idp,
    induction p using phomotopy_rec_idp,
    induction k with k k₀, induction k₀,
    reflexivity
Defined.

Definition refl_symm : (reflexivity _)^-1* = reflexivity k.
Proof.
    induction k with k k₀, induction k₀,
    reflexivity
Defined.

Definition symm_symm (p : k ==* l) : p^-1*^-1* = p.
Proof.
    induction p using phomotopy_rec_idp, induction k with k k₀, induction k₀, reflexivity
Defined.

Definition trans_right_inv (p : k ==* l) : p @* p^-1* = (reflexivity _).
Proof.
    induction p using phomotopy_rec_idp, exact !refl_trans @ !refl_symm
Defined.

Definition trans_left_inv (p : k ==* l) : p^-1* @* p = (reflexivity _).
Proof.
    induction p using phomotopy_rec_idp, exact !trans_refl @ !refl_symm
Defined.

Definition trans2 {p p' : k ==* l} {q q' : l ==* m} (r : p = p') (s : q = q') : p @* q = p' @* q'.
  ap011 phomotopy.trans r s

Definition pcompose3 {A B C : pType} {g g' : B ->* C} {f f' : A ->* B}
  {p p' : g ==* g'} {q q' : f ==* f'} (r : p = p') (s : q = q') : p ◾* q = p' ◾* q'.
  ap011 pcompose2 r s

Definition symm2 {p p' : k ==* l} (r : p = p') : p^-1* = p'^-1*.
  ap phomotopy.symm r

  infixl ` ◾** `:80 . pointed.trans2
  infixl ` ◽* `:81 . pointed.pcompose3
  postfix `⁻²**`:(max+1) . pointed.symm2

Definition trans_symm (p : k ==* l) (q : l ==* m) : (p @* q)^-1* = q^-1* @* p^-1*.
Proof.
    induction p using phomotopy_rec_idp, induction q using phomotopy_rec_idp,
    exact !trans_refl⁻²** @ !trans_refl^-1 @ idp ◾** !refl_symm^-1
Defined.

Definition phwhisker_left (p : k ==* l) {q q' : l ==* m} (s : q = q') : p @* q = p @* q'.
  idp ◾** s

Definition phwhisker_right {p p' : k ==* l} (q : l ==* m) (r : p = p') : p @* q = p' @* q.
  r ◾** idp

Definition pwhisker_left_refl {A B C : pType} (g : B ->* C) (f : A ->* B) :
    pwhisker_left g (reflexivity f) = reflexivity (g o* f).
Proof.
    induction A with A a₀, induction B with B b₀, induction C with C c₀,
    induction f with f f₀, induction g with g g₀,
    esimp at *, induction g₀, induction f₀, reflexivity
Defined.

Definition pwhisker_right_refl {A B C : pType} (f : A ->* B) (g : B ->* C) :
    pwhisker_right f (reflexivity g) = reflexivity (g o* f).
Proof.
    induction A with A a₀, induction B with B b₀, induction C with C c₀,
    induction f with f f₀, induction g with g g₀,
    esimp at *, induction g₀, induction f₀, reflexivity
Defined.

Definition pcompose2_refl {A B C : pType} (g : B ->* C) (f : A ->* B) :
    reflexivity g ◾* reflexivity f = (reflexivity _).
  !pwhisker_right_refl ◾** !pwhisker_left_refl @ !refl_trans

Definition pcompose2_refl_left {A B C : pType} (g : B ->* C) {f f' : A ->* B} (p : f ==* f') :
    (reflexivity _) ◾* p = pwhisker_left g p.
  !pwhisker_right_refl ◾** idp @ !refl_trans

Definition pcompose2_refl_right {A B C : pType} {g g' : B ->* C} (f : A ->* B) (p : g ==* g') :
    p ◾* (reflexivity _) = pwhisker_right f p.
  idp ◾** !pwhisker_left_refl @ !trans_refl

Definition pwhisker_left_trans {A B C : pType} (g : B ->* C) {f₁ f₂ f₃ : A ->* B}
    (p : f₁ ==* f₂) (q : f₂ ==* f₃) :
    pwhisker_left g (p @* q) = pwhisker_left g p @* pwhisker_left g q.
Proof.
    induction p using phomotopy_rec_idp,
    induction q using phomotopy_rec_idp,
    refine _ @ !pwhisker_left_refl^-1 ◾** !pwhisker_left_refl^-1,
    refine ap (pwhisker_left g) !trans_refl @ !pwhisker_left_refl @ !trans_refl^-1
Defined.

Definition pwhisker_right_trans {A B C : pType} (f : A ->* B) {g₁ g₂ g₃ : B ->* C}
    (p : g₁ ==* g₂) (q : g₂ ==* g₃) :
    pwhisker_right f (p @* q) = pwhisker_right f p @* pwhisker_right f q.
Proof.
    induction p using phomotopy_rec_idp,
    induction q using phomotopy_rec_idp,
    refine _ @ !pwhisker_right_refl^-1 ◾** !pwhisker_right_refl^-1,
    refine ap (pwhisker_right f) !trans_refl @ !pwhisker_right_refl @ !trans_refl^-1
Defined.

Definition pwhisker_left_symm {A B C : pType} (g : B ->* C) {f₁ f₂ : A ->* B} (p : f₁ ==* f₂) :
    pwhisker_left g p^-1* = (pwhisker_left g p)^-1*.
Proof.
    induction p using phomotopy_rec_idp,
    refine _ @ ap phomotopy.symm !pwhisker_left_refl^-1,
    refine ap (pwhisker_left g) !refl_symm @ !pwhisker_left_refl @ !refl_symm^-1
Defined.

Definition pwhisker_right_symm {A B C : pType} (f : A ->* B) {g₁ g₂ : B ->* C} (p : g₁ ==* g₂) :
    pwhisker_right f p^-1* = (pwhisker_right f p)^-1*.
Proof.
    induction p using phomotopy_rec_idp,
    refine _ @ ap phomotopy.symm !pwhisker_right_refl^-1,
    refine ap (pwhisker_right f) !refl_symm @ !pwhisker_right_refl @ !refl_symm^-1
Defined.

Definition trans_eq_of_eq_symm_trans {p : k ==* l} {q : l ==* m} {r : k ==* m} (s : q = p^-1* @* r) :
    p @* q = r.
  idp ◾** s @ !trans_assoc^-1 @ trans_right_inv p ◾** idp @ !refl_trans

Definition eq_symm_trans_of_trans_eq {p : k ==* l} {q : l ==* m} {r : k ==* m} (s : p @* q = r) :
    q = p^-1* @* r.
  !refl_trans^-1 @ !trans_left_inv^-1 ◾** idp @ !trans_assoc @ idp ◾** s

Definition trans_eq_of_eq_trans_symm {p : k ==* l} {q : l ==* m} {r : k ==* m} (s : p = r @* q^-1*) :
    p @* q = r.
  s ◾** idp @ !trans_assoc @ idp ◾** trans_left_inv q @ !trans_refl

Definition eq_trans_symm_of_trans_eq {p : k ==* l} {q : l ==* m} {r : k ==* m} (s : p @* q = r) :
    p = r @* q^-1*.
  !trans_refl^-1 @ idp ◾** !trans_right_inv^-1 @ !trans_assoc^-1 @ s ◾** idp

Definition eq_trans_of_symm_trans_eq {p : k ==* l} {q : l ==* m} {r : k ==* m} (s : p^-1* @* r = q) :
    r = p @* q.
  !refl_trans^-1 @ !trans_right_inv^-1 ◾** idp @ !trans_assoc @ idp ◾** s

Definition symm_trans_eq_of_eq_trans {p : k ==* l} {q : l ==* m} {r : k ==* m} (s : r = p @* q) :
    p^-1* @* r = q.
  idp ◾** s @ !trans_assoc^-1 @ trans_left_inv p ◾** idp @ !refl_trans

Definition eq_trans_of_trans_symm_eq {p : k ==* l} {q : l ==* m} {r : k ==* m} (s : r @* q^-1* = p) :
    r = p @* q.
  !trans_refl^-1 @ idp ◾** !trans_left_inv^-1 @ !trans_assoc^-1 @ s ◾** idp

Definition trans_symm_eq_of_eq_trans {p : k ==* l} {q : l ==* m} {r : k ==* m} (s : r = p @* q) :
    r @* q^-1* = p.
  s ◾** idp @ !trans_assoc @ idp ◾** trans_right_inv q @ !trans_refl

  section phsquare
  (*
    Squares of pointed homotopies
  *)

  variables {f f' f₀₀ f₂₀ f₄₀ f₀₂ f₂₂ f₄₂ f₀₄ f₂₄ f₄₄ : ppi P p₀}
            {p₁₀ : f₀₀ ==* f₂₀} {p₃₀ : f₂₀ ==* f₄₀}
            {p₀₁ : f₀₀ ==* f₀₂} {p₂₁ : f₂₀ ==* f₂₂} {p₄₁ : f₄₀ ==* f₄₂}
            {p₁₂ : f₀₂ ==* f₂₂} {p₃₂ : f₂₂ ==* f₄₂}
            {p₀₃ : f₀₂ ==* f₀₄} {p₂₃ : f₂₂ ==* f₂₄} {p₄₃ : f₄₂ ==* f₄₄}
            {p₁₄ : f₀₄ ==* f₂₄} {p₃₄ : f₂₄ ==* f₄₄}

Definition phsquare (p₁₀ : f₀₀ ==* f₂₀) (p₁₂ : f₀₂ ==* f₂₂)
                                  (p₀₁ : f₀₀ ==* f₀₂) (p₂₁ : f₂₀ ==* f₂₂) : Type.
  p₁₀ @* p₂₁ = p₀₁ @* p₁₂

Definition phsquare_of_eq (p : p₁₀ @* p₂₁ = p₀₁ @* p₁₂) : phsquare p₁₀ p₁₂ p₀₁ p₂₁ . p
Definition eq_of_phsquare (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : p₁₀ @* p₂₁ = p₀₁ @* p₁₂ . p

  (*Definition phsquare.mk (p : forall x, square (p₁₀ x) (p₁₂ x) (p₀₁ x) (p₂₁ x)) *)
  (*   (q : cube (square_of_eq (point_htpy p₁₀)) (square_of_eq (point_htpy p₁₂)) *)
  (*             (square_of_eq (point_htpy p₀₁)) (square_of_eq (point_htpy p₂₁)) *)
  (*             (p (point _)) ids) : phsquare p₁₀ p₁₂ p₀₁ p₂₁ . *)
  (* begin *)
  (*   fapply phomotopy_eq, *)
  (*   { intro x, apply eq_of_square (p x) }, *)
  (*   { generalize p (point _), intro r, exact sorry } *)
  (* end *)


Definition phhconcat (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) (q : phsquare p₃₀ p₃₂ p₂₁ p₄₁) :
    phsquare (p₁₀ @* p₃₀) (p₁₂ @* p₃₂) p₀₁ p₄₁.
  !trans_assoc @ idp ◾** q @ !trans_assoc^-1 @ p ◾** idp @ !trans_assoc

Definition phvconcat (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) (q : phsquare p₁₂ p₁₄ p₀₃ p₂₃) :
    phsquare p₁₀ p₁₄ (p₀₁ @* p₀₃) (p₂₁ @* p₂₃).
  (phhconcat p^-1 q^-1)^-1

Definition phhdeg_square {p₁ p₂ : f ==* f'} (q : p₁ = p₂) : phsquare (reflexivity _) (reflexivity _) p₁ p₂.
  !refl_trans @ q^-1 @ !trans_refl^-1
Definition phvdeg_square {p₁ p₂ : f ==* f'} (q : p₁ = p₂) : phsquare p₁ p₂ (reflexivity _) (reflexivity _).
  !trans_refl @ q @ !refl_trans^-1

  variables (p₀₁ p₁₀)
Definition phhrefl : phsquare (reflexivity _) (reflexivity _) p₀₁ p₀₁ . phhdeg_square idp
Definition phvrefl : phsquare p₁₀ p₁₀ (reflexivity _) (reflexivity _) . phvdeg_square idp
  variables {p₀₁ p₁₀}
Definition phhrfl : phsquare (reflexivity _) (reflexivity _) p₀₁ p₀₁ . phhrefl p₀₁
Definition phvrfl : phsquare p₁₀ p₁₀ (reflexivity _) (reflexivity _) . phvrefl p₁₀

  (*
    The names are very baroque. The following stands for
    "pointed homotopy path-horizontal composition" (i.e. composition on the left with a path)
    The names are obtained by using the ones for squares, and putting "ph" in front of it.
    In practice, use the notation @ph** defined below, which might be easier to remember
  *)
Definition phphconcat {p₀₁'} (p : p₀₁' = p₀₁) (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare p₁₀ p₁₂ p₀₁' p₂₁.
  by induction p; exact q

Definition phhpconcat {p₂₁'} (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) (p : p₂₁ = p₂₁') :
    phsquare p₁₀ p₁₂ p₀₁ p₂₁'.
  by induction p; exact q

Definition phpvconcat {p₁₀'} (p : p₁₀' = p₁₀) (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare p₁₀' p₁₂ p₀₁ p₂₁.
  by induction p; exact q

Definition phvpconcat {p₁₂'} (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) (p : p₁₂ = p₁₂') :
    phsquare p₁₀ p₁₂' p₀₁ p₂₁.
  by induction p; exact q

Definition phhinverse (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : phsquare p₁₀^-1* p₁₂^-1* p₂₁ p₀₁.
Proof.
    refine (eq_symm_trans_of_trans_eq _)^-1,
    refine !trans_assoc^-1 @ _,
    refine (eq_trans_symm_of_trans_eq _)^-1,
    exact (eq_of_phsquare p)^-1
Defined.

Definition phvinverse (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : phsquare p₁₂ p₁₀ p₀₁^-1* p₂₁^-1*.
  (phhinverse p^-1)^-1

  infix ` @h** `:78 . phhconcat
  infix ` @v** `:78 . phvconcat
  infixr ` @ph** `:77 . phphconcat
  infixl ` @hp** `:77 . phhpconcat
  infixr ` @pv** `:77 . phpvconcat
  infixl ` @vp** `:77 . phvpconcat
  postfix `^-1ʰ**`:(max+1) . phhinverse
  postfix `^-1ᵛ**`:(max+1) . phvinverse

Definition phwhisker_rt (p : f ==* f₂₀) (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare (p₁₀ @* p^-1*) p₁₂ p₀₁ (p @* p₂₁).
  !trans_assoc @ idp ◾** (!trans_assoc^-1 @ !trans_left_inv ◾** idp @ !refl_trans) @ q

Definition phwhisker_br (p : f₂₂ ==* f) (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare p₁₀ (p₁₂ @* p) p₀₁ (p₂₁ @* p).
  !trans_assoc^-1 @ q ◾** idp @ !trans_assoc

Definition phmove_top_of_left' {p₀₁ : f ==* f₀₂} (p : f₀₀ ==* f)
    (q : phsquare p₁₀ p₁₂ (p @* p₀₁) p₂₁) : phsquare (p^-1* @* p₁₀) p₁₂ p₀₁ p₂₁.
  !trans_assoc @ (eq_symm_trans_of_trans_eq (q @ !trans_assoc)^-1)^-1

Definition phmove_bot_of_left {p₀₁ : f₀₀ ==* f} (p : f ==* f₀₂)
    (q : phsquare p₁₀ p₁₂ (p₀₁ @* p) p₂₁) : phsquare p₁₀ (p @* p₁₂) p₀₁ p₂₁.
  q @ !trans_assoc

Definition passoc_phomotopy_right {A B C D : pType} (h : C ->* D) (g : B ->* C) {f f' : A ->* B}
    (p : f ==* f') : phsquare (passoc h g f) (passoc h g f')
      (pwhisker_left (h o* g) p) (pwhisker_left h (pwhisker_left g p)).
Proof.
    induction p using phomotopy_rec_idp,
    refine idp ◾** (ap (pwhisker_left h) !pwhisker_left_refl @ !pwhisker_left_refl) @ _ @
          !pwhisker_left_refl^-1 ◾** idp,
    exact !trans_refl @ !refl_trans^-1
Defined.

Definition passoc_phomotopy_middle {A B C D : pType} (h : C ->* D) {g g' : B ->* C} (f : A ->* B)
    (p : g ==* g') : phsquare (passoc h g f) (passoc h g' f)
      (pwhisker_right f (pwhisker_left h p)) (pwhisker_left h (pwhisker_right f p)).
Proof.
    induction p using phomotopy_rec_idp,
    rewrite [pwhisker_right_refl, pwhisker_left_refl],
    rewrite [pwhisker_right_refl, pwhisker_left_refl],
    exact phvrfl
Defined.

Definition pwhisker_right_pwhisker_left {A B C : pType} {g g' : B ->* C} {f f' : A ->* B}
    (p : g ==* g') (q : f ==* f') :
    phsquare (pwhisker_right f p) (pwhisker_right f' p) (pwhisker_left g q) (pwhisker_left g' q).
Proof.
    induction p using phomotopy_rec_idp,
    induction q using phomotopy_rec_idp,
    exact !pwhisker_right_refl ◾** !pwhisker_left_refl @
          !pwhisker_left_refl^-1 ◾** !pwhisker_right_refl^-1
Defined.

Defined. phsquare

  section nondep_phsquare

  variables {f f' f₀₀ f₂₀ f₀₂ f₂₂ : A ->* B}
            {p₁₀ : f₀₀ ==* f₂₀} {p₀₁ : f₀₀ ==* f₀₂} {p₂₁ : f₂₀ ==* f₂₂} {p₁₂ : f₀₂ ==* f₂₂}

Definition pwhisker_left_phsquare (f : B ->* C) (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare (pwhisker_left f p₁₀) (pwhisker_left f p₁₂)
             (pwhisker_left f p₀₁) (pwhisker_left f p₂₁).
  !pwhisker_left_trans^-1 @ ap (pwhisker_left f) p @ !pwhisker_left_trans

Definition pwhisker_right_phsquare (f : C ->* A) (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare (pwhisker_right f p₁₀) (pwhisker_right f p₁₂)
             (pwhisker_right f p₀₁) (pwhisker_right f p₂₁).
  !pwhisker_right_trans^-1 @ ap (pwhisker_right f) p @ !pwhisker_right_trans

Defined. nondep_phsquare

Definition phomotopy_path_con (p : k = l) (q : l = m) :
    phomotopy_path (p @ q) = phomotopy_path p @* phomotopy_path q.
Proof. induction q, induction p, exact !trans_refl^-1 end

Definition pcompose_left_path_pforall {A B C : pType} (g : B ->* C) {f f' : A ->* B}
    (H : f ==* f') : ap (fun f => g o* f) (path_pforall H) = path_pforall (pwhisker_left g H).
Proof.
    induction H using phomotopy_rec_idp,
    refine ap02 _ !path_pforall_refl @ !path_pforall_refl^-1 @ ap path_pforall _,
    exact !pwhisker_left_refl^-1
Defined.

Definition pcompose_right_path_pforall {A B C : pType} {g g' : B ->* C} (f : A ->* B)
    (H : g ==* g') : ap (fun g => g o* f) (path_pforall H) = path_pforall (pwhisker_right f H).
Proof.
    induction H using phomotopy_rec_idp,
    refine ap02 _ !path_pforall_refl @ !path_pforall_refl^-1 @ ap path_pforall _,
    exact !pwhisker_right_refl^-1
Defined.

Definition phomotopy_path_pcompose_left {A B C : pType} (g : B ->* C) {f f' : A ->* B}
    (p : f = f') : phomotopy_path (ap (fun f => g o* f) p) = pwhisker_left g (phomotopy_path p).
Proof.
    induction p, exact !pwhisker_left_refl^-1
Defined.

Definition phomotopy_path_pcompose_right {A B C : pType} {g g' : B ->* C} (f : A ->* B)
    (p : g = g') : phomotopy_path (ap (fun g => g o* f) p) = pwhisker_right f (phomotopy_path p).
Proof.
    induction p, exact !pwhisker_right_refl^-1
Defined.

Definition phomotopy_mk_ppMap {A B C : pType} {f g : A ->* ppMap B C} (p : forall a, f a ==* g a)
    (q : p (point _) @* phomotopy_path (point_eq g) = phomotopy_path (point_eq f))
    : f ==* g.
Proof.
    apply Build_pHomotopy (fun a => path_pforall (p a)),
    apply eq_of_fn_eq_fn (pmap_eq_equiv _ _), esimp [pmap_eq_equiv],
    refine !phomotopy_path_con @ _,
    refine !phomotopy_path_of_phomotopy ◾** idp @ q,
Defined.

  (* properties of ppMap, the pointed type of pointed maps *)
Definition pcompose_pconst (f : B ->* C) : f o* pconst A B ==* pconst A C.
  Build_pHomotopy (fun a => point_eq f) (idp_con _)^-1

Definition pconst_pcompose (f : A ->* B) : pconst B C o* f ==* pconst A C.
  Build_pHomotopy (fun a => rfl) (ap_pp _ _ _)stant^-1

Definition ppcompose_left (g : B ->* C) : ppMap A B ->* ppMap A C.
  Build_pMap (pcompose g) (path_pforall (pcompose_pconst g))

Definition ppcompose_right (f : A ->* B) : ppMap B C ->* ppMap A C.
  Build_pMap (fun g => g o* f) (path_pforall (pconst_pcompose f))

  (* TODO: give construction using pequiv.MK, which computes better (see comment for a start of the proof), rename to ppMap_pequiv_ppMap_right *)
Definition pequiv_ppcompose_left (g : B <~>* C) : ppMap A B <~>* ppMap A C.
  pequiv.MK' (ppcompose_left g) (ppcompose_left g^-1ᵉ*)
    begin intro f, apply path_pforall, apply pinv_pcompose_cancel_left end
    begin intro f, apply path_pforall, apply pcompose_pinv_cancel_left end
  (* pequiv.MK (ppcompose_left g) (ppcompose_left g^-1ᵉ*) *)
  (*   abstract begin *)
  (*     apply phomotopy_mk_ppMap (pinv_pcompose_cancel_left g), esimp, *)
  (*     refine !trans_refl @ _, *)
  (*     refine _ @ (!phomotopy_path_con @ (!phomotopy_path_pcompose_left @ *)
  (*       ap (pwhisker_left _) !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy)^-1, *)

  (*   end end *)
  (*   abstract begin *)
  (*     exact sorry *)
  (*   end end *)

Definition pequiv_ppcompose_right (f : A <~>* B) : ppMap B C <~>* ppMap A C.
Proof.
    fapply pequiv.MK',
    { exact ppcompose_right f },
    { exact ppcompose_right f^-1ᵉ* },
    { intro g, apply path_pforall, apply pcompose_pinv_cancel_right },
    { intro g, apply path_pforall, apply pinv_pcompose_cancel_right },
Defined.

Definition loop_ppMap_commute (A B : pType) : Ω(ppMap A B) <~>* (ppMap A (loops B)).
    pequiv_of_equiv
      (calc Ω(ppMap A B) <~> (pconst A B ==* pconst A B)                       : pmap_eq_equiv _ _
                     ... <~> Σ(p : pconst A B == pconst A B), p (point _) @ rfl = rfl : phomotopy.sigma_char
                     ... <~> (A ->* loops B)                                       : pmap.sigma_char)
      (by reflexivity)

Definition papply {A : pType} (B : pType) (a : A) : ppMap A B ->* B.
  Build_pMap (fun (f : A ->* B) => f a) idp

Definition papply_pcompose {A : pType} (B : pType) (a : A) : ppMap A B ->* B.
  Build_pMap (fun (f : A ->* B) => f a) idp

Definition ppMap_pbool_pequiv (B : pType) : ppMap pbool B <~>* B.
Proof.
    fapply pequiv.MK',
    { exact papply B tt },
    { exact pbool_pmap },
    { intro f, fapply path_pforall, fapply Build_pHomotopy,
      { intro b, cases b, exact !point_eq^-1, reflexivity },
      { exact (con_Vp _) }},
    { intro b, reflexivity },
Defined.

Definition papn_pt (n : ℕ) (A B : pType) : ppMap A B ->* ppMap (Ω[n] A) (Ω[n] B).
  Build_pMap (fun f => apn n f) (path_pforall !apn_pconst)

Definition papn_fun {n : ℕ} {A : pType} (B : pType) (p : Ω[n] A) :
    ppMap A B ->* Ω[n] B.
  papply _ p o* papn_pt n A B

Definition pconst_pcompose_pconst (A B C : pType) :
    pconst_pcompose (pconst A B) = pcompose_pconst (pconst B C).
  idp

Definition pconst_pcompose_phomotopy_pconst {A B C : pType} {f : A ->* B} (p : f ==* pconst A B) :
    pconst_pcompose f = pwhisker_left (pconst B C) p @* pcompose_pconst (pconst B C).
Proof.
    assert H : forall (p : pconst A B ==* f),
      pconst_pcompose f = pwhisker_left (pconst B C) p^-1* @* pcompose_pconst (pconst B C),
    { intro p, induction p using phomotopy_rec_idp, reflexivity },
    refine H p^-1* @ ap (pwhisker_left _) !symm_symm ◾** idp,
Defined.

Definition passoc_pconst_right {A B C D : pType} (h : C ->* D) (g : B ->* C) :
    passoc h g (pconst A B) @* (pwhisker_left h (pcompose_pconst g) @* pcompose_pconst h) =
    pcompose_pconst (h o* g).
Proof.
    fapply phomotopy_eq,
    { intro a, exact (concat_1p _) },
    { induction h with h h₀, induction g with g g₀, induction D with D d₀, induction C with C c₀,
      esimp at *, induction g₀, induction h₀, reflexivity }
Defined.

Definition passoc_pconst_middle {A A' B B' : pType} (g : B ->* B') (f : A' ->* A) :
    passoc g (pconst A B) f @* (pwhisker_left g (pconst_pcompose f) @* pcompose_pconst g) =
    pwhisker_right f (pcompose_pconst g) @* pconst_pcompose f.
Proof.
    fapply phomotopy_eq,
    { intro a, exact (concat_1p _) @ (concat_1p _) },
    { induction g with g g₀, induction f with f f₀, induction B' with D d₀, induction A with C c₀,
      esimp at *, induction g₀, induction f₀, reflexivity }
Defined.

Definition passoc_pconst_left {A B C D : pType} (g : B ->* C) (f : A ->* B) :
    phsquare (passoc (pconst C D) g f) (pconst_pcompose f)
             (pwhisker_right f (pconst_pcompose g)) (pconst_pcompose (g o* f)).
Proof.
    fapply phomotopy_eq,
    { intro a, exact (concat_1p _) },
    { induction g with g g₀, induction f with f f₀, induction C with C c₀, induction B with B b₀,
      esimp at *, induction g₀, induction f₀, reflexivity }
Defined.

Definition ppcompose_left_pcompose {A B C D : pType} (h : C ->* D) (g : B ->* C) :
    @ppcompose_left A _ _ (h o* g) ==* ppcompose_left h o* ppcompose_left g.
Proof.
    fapply phomotopy_mk_ppMap,
    { exact passoc h g },
    { refine idp ◾** (!phomotopy_path_con @
        (ap phomotopy_path !pcompose_left_path_pforall @ !phomotopy_path_of_phomotopy) ◾**
        !phomotopy_path_of_phomotopy) @ _ @ !phomotopy_path_of_phomotopy^-1,
      exact passoc_pconst_right h g }
Defined.

Definition ppcompose_right_pcompose {A B C D : pType} (g : B ->* C) (f : A ->* B) :
    @ppcompose_right _ _ D (g o* f) ==* ppcompose_right f o* ppcompose_right g.
Proof.
    symmetry,
    fapply phomotopy_mk_ppMap,
    { intro h, exact passoc h g f },
    { refine idp ◾** !phomotopy_path_of_phomotopy @ _ @ (!phomotopy_path_con @
        (ap phomotopy_path !pcompose_right_path_pforall @ !phomotopy_path_of_phomotopy) ◾** !phomotopy_path_of_phomotopy)^-1,
      exact passoc_pconst_left g f }
Defined.

Definition ppcompose_left_ppcompose_right {A A' B B' : pType} (g : B ->* B') (f : A' ->* A) :
    psquare (ppcompose_left g) (ppcompose_left g) (ppcompose_right f) (ppcompose_right f).
Proof.
    fapply phomotopy_mk_ppMap,
    { intro h, exact passoc g h f },
    { refine idp ◾** (!phomotopy_path_con @
        (ap phomotopy_path !pcompose_left_path_pforall @ !phomotopy_path_of_phomotopy) ◾**
        !phomotopy_path_of_phomotopy) @ _ @ (!phomotopy_path_con @
        (ap phomotopy_path !pcompose_right_path_pforall @ !phomotopy_path_of_phomotopy) ◾**
        !phomotopy_path_of_phomotopy)^-1,
      apply passoc_pconst_middle }
Defined.

Definition pcompose_pconst_phomotopy {A B C : pType} {f f' : B ->* C} (p : f ==* f') :
    pwhisker_right (pconst A B) p @* pcompose_pconst f' = pcompose_pconst f.
Proof.
    fapply phomotopy_eq,
    { intro a, exact point_htpy p },
    { induction p using phomotopy_rec_idp, induction C with C c₀, induction f with f f₀,
      esimp at *, induction f₀, reflexivity }
Defined.

Definition pid_pconst (A B : pType) : pcompose_pconst (pid B) = pid_pcompose (pconst A B).
  by reflexivity

Definition pid_pconst_pcompose {A B C : pType} (f : A ->* B) :
    phsquare (pid_pcompose (pconst B C o* f))
             (pcompose_pconst (pid C))
             (pwhisker_left (pid C) (pconst_pcompose f))
             (pconst_pcompose f).
Proof.
    fapply phomotopy_eq,
    { reflexivity },
    { induction f with f f₀, induction B with B b₀, esimp at *, induction f₀, reflexivity }
Defined.

Definition ppcompose_left_pconst (A B C : pType) :
    @ppcompose_left A _ _ (pconst B C) ==* pconst (ppMap A B) (ppMap A C).
Proof.
    fapply phomotopy_mk_ppMap,
    { exact pconst_pcompose },
    { refine idp ◾** !phomotopy_path_idp @ !phomotopy_path_of_phomotopy^-1 }
Defined.

Definition ppcompose_left_phomotopy {A B C : pType} {g g' : B ->* C} (p : g ==* g') :
    @ppcompose_left A _ _ g ==* ppcompose_left g'.
Proof.
    induction p using phomotopy_rec_idp,
    reflexivity
Defined.

Definition ppcompose_left_phomotopy_refl {A B C : pType} (g : B ->* C) :
    ppcompose_left_phomotopy (reflexivity g) = reflexivity (@ppcompose_left A _ _ g).
  !phomotopy_rec_idp_refl

    (* a more explicit proof of ppcompose_left_phomotopy, which might be useful if we need to prove properties about it
    *)
    (* fapply phomotopy_mk_ppMap, *)
    (* { intro f, exact pwhisker_right f p }, *)
    (* { refine ap (fun x => _ @* x) !phomotopy_path_of_phomotopy @ _ @ !phomotopy_path_of_phomotopy^-1, *)
    (*   exact pcompose_pconst_phomotopy p } *)

Definition ppcompose_right_phomotopy {A B C : pType} {f f' : A ->* B} (p : f ==* f') :
    @ppcompose_right _ _ C f ==* ppcompose_right f'.
Proof.
    induction p using phomotopy_rec_idp,
    reflexivity
Defined.

Definition pppcompose (A B C : pType) : ppMap B C ->* ppMap (ppMap A B) (ppMap A C).
  Build_pMap ppcompose_left (path_pforall !ppcompose_left_pconst)

  section psquare

  variables {A' A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : pType}
            {f₁₀ f₁₀' : A₀₀ ->* A₂₀} {f₃₀ : A₂₀ ->* A₄₀}
            {f₀₁ f₀₁' : A₀₀ ->* A₀₂} {f₂₁ f₂₁' : A₂₀ ->* A₂₂} {f₄₁ : A₄₀ ->* A₄₂}
            {f₁₂ f₁₂' : A₀₂ ->* A₂₂} {f₃₂ : A₂₂ ->* A₄₂}
            {f₀₃ : A₀₂ ->* A₀₄} {f₂₃ : A₂₂ ->* A₂₄} {f₄₃ : A₄₂ ->* A₄₄}
            {f₁₄ : A₀₄ ->* A₂₄} {f₃₄ : A₂₄ ->* A₄₄}

Definition ppcompose_left_psquare {A : pType} (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (@ppcompose_left A _ _ f₁₀) (ppcompose_left f₁₂)
            (ppcompose_left f₀₁) (ppcompose_left f₂₁).
  !ppcompose_left_pcompose^-1* @* ppcompose_left_phomotopy p @* !ppcompose_left_pcompose

Definition ppcompose_right_psquare {A : pType} (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (@ppcompose_right _ _ A f₁₂) (ppcompose_right f₁₀)
            (ppcompose_right f₂₁) (ppcompose_right f₀₁).
  !ppcompose_right_pcompose^-1* @* ppcompose_right_phomotopy p^-1* @* !ppcompose_right_pcompose

Definition trans_phomotopy_hconcat {f₀₁' f₀₁''}
    (q₂ : f₀₁'' ==* f₀₁') (q₁ : f₀₁' ==* f₀₁) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    (q₂ @* q₁) @ph* p = q₂ @ph* q₁ @ph* p.
  idp ◾** (ap (pwhisker_left f₁₂) !trans_symm @ !pwhisker_left_trans) @ !trans_assoc^-1

Definition symm_phomotopy_hconcat {f₀₁'} (q : f₀₁ ==* f₀₁')
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : q^-1* @ph* p = p @* pwhisker_left f₁₂ q.
  idp ◾** ap (pwhisker_left f₁₂) !symm_symm

Definition refl_phomotopy_hconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : (reflexivity _) @ph* p = p.
  idp ◾** (ap (pwhisker_left _) !refl_symm @ !pwhisker_left_refl) @ !trans_refl

  local attribute (reflexivity _) [reducible]
Definition pwhisker_left_phomotopy_hconcat {f₀₁'} (r : f₀₁' ==* f₀₁)
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare f₁₂ f₁₄ f₀₃ f₂₃) :
    pwhisker_left f₀₃ r @ph* (p @v* q) = (r @ph* p) @v* q.
  by induction r using phomotopy_rec_idp; rewrite [pwhisker_left_refl, +refl_phomotopy_hconcat]

Definition pvcompose_pwhisker_left {f₀₁'} (r : f₀₁ ==* f₀₁')
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare f₁₂ f₁₄ f₀₃ f₂₃) :
    (p @v* q) @* (pwhisker_left f₁₄ (pwhisker_left f₀₃ r)) = (p @* pwhisker_left f₁₂ r) @v* q.
  by induction r using phomotopy_rec_idp; rewrite [+pwhisker_left_refl, + trans_refl]

Definition phconcat2 {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁} {q q' : psquare f₃₀ f₃₂ f₂₁ f₄₁}
    (r : p = p') (s : q = q') : p @h* q = p' @h* q'.
  ap011 phconcat r s

Definition pvconcat2 {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁} {q q' : psquare f₁₂ f₁₄ f₀₃ f₂₃}
    (r : p = p') (s : q = q') : p @v* q = p' @v* q'.
  ap011 pvconcat r s

Definition phinverse2 {f₁₀ : A₀₀ <~>* A₂₀} {f₁₂ : A₀₂ <~>* A₂₂} {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁}
    (r : p = p') : p^-1ʰ* = p'^-1ʰ*.
  ap phinverse r

Definition pvinverse2 {f₀₁ : A₀₀ <~>* A₀₂} {f₂₁ : A₂₀ <~>* A₂₂} {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁}
    (r : p = p') : p^-1ᵛ* = p'^-1ᵛ*.
  ap pvinverse r

Definition phomotopy_hconcat2 {q q' : f₀₁' ==* f₀₁} {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁}
    (r : q = q') (s : p = p') : q @ph* p = q' @ph* p'.
  ap011 phomotopy_hconcat r s

Definition hconcat_phomotopy2 {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁} {q q' : f₂₁' ==* f₂₁}
    (r : p = p') (s : q = q') : p @hp* q = p' @hp* q'.
  ap011 hconcat_phomotopy r s

Definition phomotopy_vconcat2 {q q' : f₁₀' ==* f₁₀} {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁}
    (r : q = q') (s : p = p') : q @pv* p = q' @pv* p'.
  ap011 phomotopy_vconcat r s

Definition vconcat_phomotopy2 {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁} {q q' : f₁₂' ==* f₁₂}
    (r : p = p') (s : q = q') : p @vp* q = p' @vp* q'.
  ap011 vconcat_phomotopy r s

  (* for consistency, should there be a second star here? *)
  infix ` ◾h* `:79 . phconcat2
  infix ` ◾v* `:79 . pvconcat2
  infixl ` ◾hp* `:79 . hconcat_phomotopy2
  infixr ` ◾ph* `:79 . phomotopy_hconcat2
  infixl ` ◾vp* `:79 . vconcat_phomotopy2
  infixr ` ◾pv* `:79 . phomotopy_vconcat2
  postfix `⁻²ʰ*`:(max+1) . phinverse2
  postfix `⁻²ᵛ*`:(max+1) . pvinverse2

Defined. psquare

  variables {X X' Y Y' Z : pType}
Definition pap1 (X Y : pType) : ppMap X Y ->* ppMap (loops X) (loops Y).
  Build_pMap ap1 (path_pforall !ap1_pconst)

Definition ap1_gen_const {A B : Type} {a₁ a₂ : A} (b : B) (p : a₁ = a₂) :
    ap1_gen (const A b) idp idp p = idp.
  ap1_gen_idp_left (const A b) p @ ap_constant p b

Definition ap1_gen_compose_const_left
    {A B C : Type} (c : C) (f : A -> B) {a₁ a₂ : A} (p : a₁ = a₂) :
    ap1_gen_compose (const B c) f idp idp idp idp p @
    ap1_gen_const c (ap1_gen f idp idp p) =
    ap1_gen_const c p.
Proof. induction p, reflexivity end

Definition ap1_gen_compose_const_right
    {A B C : Type} (g : B -> C) (b : B) {a₁ a₂ : A} (p : a₁ = a₂) :
    ap1_gen_compose g (const A b) idp idp idp idp p @
    ap (ap1_gen g idp idp) (ap1_gen_const b p) =
    ap1_gen_const (g b) p.
Proof. induction p, reflexivity end

Definition ap1_pcompose_pconst_left {A B C : pType} (f : A ->* B) :
    phsquare (ap1_pcompose (pconst B C) f)
             (ap1_pconst A C)
             (ap1_phomotopy (pconst_pcompose f))
             (pwhisker_right (Ω-> f) (ap1_pconst B C) @* pconst_pcompose (Ω-> f)).
Proof.
    induction A with A a₀, induction B with B b₀, induction C with C c₀, induction f with f f₀,
    esimp at *, induction f₀,
    refine idp ◾** !trans_refl @ _ @ !refl_trans^-1 @ !ap1_phomotopy_refl^-1 ◾** idp,
    fapply phomotopy_eq,
    { exact ap1_gen_compose_const_left c₀ f },
    { reflexivity }
Defined.

Definition ap1_pcompose_pconst_right {A B C : pType} (g : B ->* C) :
    phsquare (ap1_pcompose g (pconst A B))
             (ap1_pconst A C)
             (ap1_phomotopy (pcompose_pconst g))
             (pwhisker_left (Ω-> g) (ap1_pconst A B) @* pcompose_pconst (Ω-> g)).
Proof.
    induction A with A a₀, induction B with B b₀, induction C with C c₀, induction g with g g₀,
    esimp at *, induction g₀,
    refine idp ◾** !trans_refl @ _ @ !refl_trans^-1 @ !ap1_phomotopy_refl^-1 ◾** idp,
    fapply phomotopy_eq,
    { exact ap1_gen_compose_const_right g b₀ },
    { reflexivity }
Defined.

Definition pap1_natural_left (f : X' ->* X) :
    psquare (pap1 X Y) (pap1 X' Y) (ppcompose_right f) (ppcompose_right (Ω-> f)).
Proof.
    fapply phomotopy_mk_ppMap,
    { intro g, exact !ap1_pcompose^-1* },
    { refine idp ◾** (ap phomotopy_path (!ap1_path_pforall  ◾ idp @ !path_pforall_trans^-1) @
      !phomotopy_path_of_phomotopy)  @ _ @ (ap phomotopy_path (!pcompose_right_path_pforall ◾
      idp @ !path_pforall_trans^-1) @ !phomotopy_path_of_phomotopy)^-1,
      apply symm_trans_eq_of_eq_trans, exact (ap1_pcompose_pconst_left f)^-1 }
Defined.

Definition pap1_natural_right (f : Y ->* Y') :
    psquare (pap1 X Y) (pap1 X Y') (ppcompose_left f) (ppcompose_left (Ω-> f)).
Proof.
    fapply phomotopy_mk_ppMap,
    { intro g, exact !ap1_pcompose^-1* },
    { refine idp ◾** (ap phomotopy_path (!ap1_path_pforall  ◾ idp @ !path_pforall_trans^-1) @
      !phomotopy_path_of_phomotopy)  @ _ @ (ap phomotopy_path (!pcompose_left_path_pforall ◾
      idp @ !path_pforall_trans^-1) @ !phomotopy_path_of_phomotopy)^-1,
      apply symm_trans_eq_of_eq_trans, exact (ap1_pcompose_pconst_right f)^-1 }
Defined.

  open sigma.ops prod
Definition pequiv.sigma_char {A B : pType} :
    (A <~>* B) <~> Σ(f : A ->* B), (Σ(g : B ->* A), f o* g ==* pid B) \* (Σ(h : B ->* A), h o* f ==* pid A).
Proof.
    fapply equiv.MK,
    { intro f, exact ⟨f, (⟨pequiv.to_pinv1 f, pequiv.pright_inv f⟩,
                          ⟨pequiv.to_pinv2 f, pequiv.pleft_inv f⟩)⟩, },
    { intro f, exact pequiv.mk' f.1 (pr1 f.2).1 (pr2 f.2).1 (pr1 f.2).2 (pr2 f.2).2 },
    { intro f, induction f with f v, induction v with hl hr, induction hl, induction hr,
      reflexivity },
    { intro f, induction f, reflexivity }
Defined.

Definition is_contr_pright_inv (f : A <~>* B) : is_contr (Σ(g : B ->* A), f o* g ==* pid B).
Proof.
    fapply is_trunc_equiv_closed,
      { exact !fiber.sigma_char @e sigma_equiv_sigma_right (fun g => !pmap_eq_equiv) },
    fapply is_contr_fiber_of_is_equiv,
    exact pequiv.to_is_equiv (pequiv_ppcompose_left f)
Defined.

Definition is_contr_pleft_inv (f : A <~>* B) : is_contr (Σ(h : B ->* A), h o* f ==* pid A).
Proof.
    fapply is_trunc_equiv_closed,
      { exact !fiber.sigma_char @e sigma_equiv_sigma_right (fun g => !pmap_eq_equiv) },
    fapply is_contr_fiber_of_is_equiv,
    exact pequiv.to_is_equiv (pequiv_ppcompose_right f)
Defined.

Definition pequiv_eq_equiv (f g : A <~>* B) : (f = g) <~> f ==* g.
  have forall (f : A ->* B), is_prop ((Σ(g : B ->* A), f o* g ==* pid B) \* (Σ(h : B ->* A), h o* f ==* pid A)),
Proof.
    intro f, apply is_prop_of_imp_is_contr, intro v,
    let f' . pequiv.sigma_char^-1ᵉ ⟨f, v⟩,
    apply is_trunc_prod, exact is_contr_pright_inv f', exact is_contr_pleft_inv f'
Defined.,
  calc (f = g) <~> (pequiv.sigma_char f = pequiv.sigma_char g)
                 : eq_equiv_fn_eq pequiv.sigma_char f g
          ...  <~> (f = g :> (A ->* B)) : subtype_eq_equiv
          ...  <~> (f ==* g) : pmap_eq_equiv f g

Definition pequiv_eq {f g : A <~>* B} (H : f ==* g) : f = g.
  (pequiv_eq_equiv f g)^-1ᵉ H

  open algebra
Definition pequiv_of_isomorphism_of_eq {G₁ G₂ : Group} (p : G₁ = G₂) :
    pequiv_of_isomorphism (isomorphism_of_eq p) = pequiv_of_eq (ap pType_of_Group p).
Proof.
    induction p,
    apply pequiv_eq,
    fapply Build_pHomotopy,
    { intro g, reflexivity },
    { apply is_prop.elim }
Defined.

Defined. pointed
