(* Exact couples of graded (left-) R-modules. This file includes:
  - Constructing exact couples from sequences of maps
  - Deriving an exact couple
  - The convergenceDefinition for exact couples *)

(* Author: Floris van Doorn *)

import .graded ..spectrum.basic .product_group .ring

open algebra is_trunc left_module is_equiv equiv eq function nat sigma set_quotient group
  left_module

(* exact couples *)

namespace exact_couple

  structure exact_couple (R : Ring) (I : AddAbGroup) : Type.
  (D E : graded_module R I)
  (i : D ->gm D) (j : D ->gm E) (k : E ->gm D)
  (ij : is_exact_gmod i j)
  (jk : is_exact_gmod j k)
  (ki : is_exact_gmod k i)

  open exact_couple.exact_couple

Definition exact_couple_reindex {R : Ring} {I J : AddAbGroup}
  (e : AddGroup_of_AddAbGroup J <~>g AddGroup_of_AddAbGroup I)
  (X : exact_couple R I) : exact_couple R J.
  (exact_couple, D . fun y => D X (e y), E . fun y => E X (e y),
  i . graded_hom_reindex e (i X),
  j . graded_hom_reindex e (j X),
  k . graded_hom_reindex e (k X),
  ij . is_exact_gmod_reindex e (ij X),
  jk . is_exact_gmod_reindex e (jk X),
  ki . is_exact_gmod_reindex e (ki X))

  namespace derived_couple
  section

  parameters {R : Ring} {I : AddAbGroup} (X : exact_couple R I)
  local abbreviation D . D X
  local abbreviation E . E X
  local abbreviation i . i X
  local abbreviation j . j X
  local abbreviation k . k X
  local abbreviation ij . ij X
  local abbreviation jk . jk X
  local abbreviation ki . ki X

Definition d : E ->gm E . j ogm k
Definition D' : graded_module R I . graded_image i
Definition E' : graded_module R I . graded_homology d d

Definition is_contr_E' {x : I} (H : is_contr (E x)) : is_contr (E' x).
  is_contr_homology _ _ _

Definition is_contr_D' {x : I} (H : is_contr (D x)) : is_contr (D' x).
  is_contr_image_module _ _

Definition E'_isomorphism {x : I} (H1 : is_contr (E ((deg d)^-1ᵉ x)))
  (H2 : is_contr (E (deg d x))) : E' x <~>lm E x.
  homology_isomorphism _ _ H1 H2

Definition i' : D' ->gm D'.
  graded_image_lift i ogm  graded_submodule_incl (fun x => image (i ← x))

  lemma is_surjective_i' {x y : I} (p : deg i' x = y)
  (H : forall (z) (q : deg i z = x), is_surjective (i ↘ q)) : is_surjective (i' ↘ p).
Proof.
  apply is_surjective_graded_hom_compose,
  { intro y q, apply is_surjective_graded_image_lift },
  { intro y q, apply is_surjective_of_is_equiv,
  induction q,
  exact to_is_equiv (equiv_of_isomorphism (image_module_isomorphism (i ← x) (H _)))
  }
Defined.

  lemma j_lemma1 (x : I) (m : D x) : d ((deg j) x) (j x m) = 0.
Proof.
  rewrite [graded_hom_compose_fn,↑d,graded_hom_compose_fn],
  refine ap (graded_hom_fn j (deg k (deg j x))) _ @
  !to_respect_zero,
  exact compose_constant.elim (gmod_im_in_ker (jk)) x m
Defined.

  lemma j_lemma2 : forall (x : I) (m : D x) (p : i x m = 0),
  (graded_homology_intro _ _ ogm graded_hom_lift _ j j_lemma1) x m = 0 :> E' _.
Proof.
  have forall (x y : I) (q : deg k x = y) (r : deg d x = deg j y)
  (s : ap (deg j) q = r) (m : D y) (p : i y m = 0), image (d ↘ r) (j y m),
Proof.
  intros, induction s, induction q,
  note m_in_im_k . is_exact.ker_in_im (ki idp _) _ p,
  induction m_in_im_k with e q,
  induction q,
  apply image.mk e idp
Defined.,
  have forall (x : I) (m : D x) (p : i x m = 0), image (d ← (deg j x)) (j x m),
Proof.
  intros,
  refine this _ _ _ p,
  exact to_right_inv (deg k) _ @ to_left_inv (deg j) x,
  apply is_set.elim
  (* rewrite [ap_con, -adj], *)
Defined.,
  intros,
  rewrite [graded_hom_compose_fn],
  exact @quotient_map_eq_zero _ _ _ _ _ (this p)
Defined.

Definition j' : D' ->gm E'.
  graded_image_elim (graded_homology_intro d d ogm graded_hom_lift _ j j_lemma1) j_lemma2
  (* degree deg j - deg i *)

  lemma k_lemma1 (x : I) (m : E x) (p : d x m = 0) : image (i ← (deg k x)) (k x m).
  gmod_ker_in_im (exact_couple.ij X) (k x m) p

Definition k₂ : graded_kernel d ->gm D' . graded_submodule_functor k k_lemma1

  lemma k_lemma2 (x : I) (m : E x) (h₁ : lm_kernel (d x) m) (h₂ : image (d ← x) m) :
  k₂ x ⟨m, h₁⟩ = 0.
Proof.
  assert H₁ : forall (x' y z w : I) (p : deg k x' = y) (q : deg j y = z) (r : deg k z = w) (n : E x'),
  k ↘ r (j ↘ q (k ↘ p n)) = 0,
  { intros, exact gmod_im_in_ker (exact_couple.jk X) q r (k ↘ p n) },
  induction h₂ with n p,
  assert H₂ : k x m = 0,
  { rewrite [-p], refine ap (k x) (graded_hom_compose_fn_out j k x n) @ _, apply H₁ },
  exact subtype_eq H₂
Defined.

Definition k' : E' ->gm D'.
  @graded_quotient_elim _ _ _ _ _ _ k₂
  (by intro x m h; cases m with [m1, m2]; exact k_lemma2 m1 m2 h)

  open sigma.ops
Definition i'_eq (x : I) (m : D x) (h : image (i ← x) m) : (i' x ⟨m, h⟩).1 = i x m.
  by reflexivity

Definition k'_eq (x : I) (m : E x) (h : d x m = 0) : (k' x (class_of ⟨m, h⟩)).1 = k x m.
  by reflexivity

  lemma j'_eq {x : I} (m : D x) : j' ↘ (ap (deg j) (left_inv (deg i) x)) (graded_image_lift i x m) =
  class_of (graded_hom_lift _ j proof j_lemma1 qed x m).
Proof.
  refine graded_image_elim_destruct _ _ _ idp _ m,
  apply is_set.elim,
Defined.

Definition deg_i' : deg i' == deg i . by reflexivity
Definition deg_j' : deg j' == deg j o (deg i)^-1 . by reflexivity
Definition deg_k' : deg k' == deg k . by reflexivity

  open group
  set_option pp.coercions true
  lemma i'j' : is_exact_gmod i' j'.
Proof.
  intro x, refine equiv_rect (deg i) _ _,
  intros y z p q, revert z q x p,
  refine eq.rec_grading (deg i @e deg j') (deg j) (ap (deg j) (left_inv (deg i) y)) _,
  intro x, revert y, refine eq.rec_equiv (deg i) _,
  apply transport (fun x => is_exact_mod x _) (idpath (i' x)),
  apply transport (fun x => is_exact_mod _ (j' ↘ (ap (deg j) (left_inv (deg i) x)))) (idpath x),
  apply is_exact_mod.mk,
  { revert x, refine equiv_rect (deg i) _ _, intro x,
  refine graded_image.rec _, intro m,
  transitivity j' ↘ _ (graded_image_lift i (deg i x) (i x m)),
  apply ap (fun x => j' ↘ _ x), apply subtype_eq, apply i'_eq,
  refine !j'_eq @ _,
  apply ap class_of, apply subtype_eq, exact is_exact.im_in_ker (exact_couple.ij X idp idp) m },
  { revert x, refine equiv_rect (deg k) _ _, intro x,
  refine graded_image.rec _, intro m p,
  assert q : graded_homology_intro d d (deg j (deg k x))
  (graded_hom_lift _ j j_lemma1 (deg k x) m) = 0,
  { exact !j'_eq^-1 @ p },
  note q2 . image_of_graded_homology_intro_eq_zero idp (graded_hom_lift _ j _ _ m) q,
  induction q2 with n r,
  assert s : j (deg k x) (m - k x n) = 0,
  { refine respect_sub (j (deg k x)) m (k x n) @ _,
  refine ap (sub _) r @ _, apply sub_self },
  assert t : trunctype.carrier (image (i ← (deg k x)) (m - k x n)),
  { exact is_exact.ker_in_im (exact_couple.ij X _ _) _ s },
  refine image.mk ⟨m - k x n, t⟩ _,
  apply subtype_eq, refine !i'_eq @ !to_respect_sub @ _,
  refine ap (@sub (D (deg i (deg k x))) _ _) _ @ @sub_zero _ _ _,
  apply is_exact.im_in_ker (exact_couple.ki X _ _) }
Defined.

  lemma j'k' : is_exact_gmod j' k'.
Proof.
  refine equiv_rect (deg i) _ _,
  intros x y z p, revert y p z,
  refine eq.rec_grading (deg i @e deg j') (deg j) (ap (deg j) (left_inv (deg i) x)) _,
  intro z q, induction q,
  apply is_exact_mod.mk,
  { refine graded_image.rec _, intro m,
  refine ap (k' _) (j'_eq m) @ _,
  apply subtype_eq,
  refine k'_eq _ _ @ _,
  exact is_exact.im_in_ker (exact_couple.jk X idp idp) m },
  { intro m p, induction m using set_quotient.rec_prop with m,
  induction m with m h, note q . (k'_eq m h)^-1 @ ap pr1 p,
  induction is_exact.ker_in_im (exact_couple.jk X idp idp) m q with n r,
  apply image.mk (graded_image_lift i x n),
  refine !j'_eq @ _,
  apply ap class_of, apply subtype_eq, exact r }
Defined.

  lemma k'i' : is_exact_gmod k' i'.
Proof.
  apply is_exact_gmod.mk,
  { intro x m, induction m using set_quotient.rec_prop with m,
  cases m with m p, apply subtype_eq,
  change i (deg k x) (k x m) = 0,
  exact is_exact.im_in_ker (exact_couple.ki X idp idp) m },
  { intro x m, induction m with m h, intro p,
  have i (deg k x) m = 0, from ap pr1 p,
  induction is_exact.ker_in_im (exact_couple.ki X idp idp) m this with n q,
  have j (deg k x) m = 0, from @(is_exact.im_in_ker2 (exact_couple.ij X _ _)) m h,
  have d x n = 0, from ap (j (deg k x)) q @ this,
  exact image.mk (class_of ⟨n, this⟩) (subtype_eq q) }
Defined.

Defined.
Defined. derived_couple

  open derived_couple

Definition derived_couple {R : Ring} {I : AddAbGroup}
  (X : exact_couple R I) : exact_couple R I.
  (exact_couple, D . D' X, E . E' X, i . i' X, j . j' X, k . k' X,
  ij . i'j' X, jk . j'k' X, ki . k'i' X)

  (* if an exact couple is bounded, we can prove the convergenceDefinition for it *)
  structure is_bounded {R : Ring} {I : AddAbGroup} (X : exact_couple R I) : Type.
  mk' :: (B B' : I -> ℕ)
  (Dub : forall (x y) (s : ℕ), (deg (i X))^[s] x = y -> B x ≤ s -> is_contr (D X y))
  (Dlb : forall (x y z) (s : ℕ) (p : deg (i X) x = y), (deg (i X))^[s] y = z -> B' z ≤ s ->
  is_surjective (i X ↘ p))
  (Elb : forall (x y) (s : ℕ), (deg (i X))^-1ᵉ^[s] x = y -> B x ≤ s -> is_contr (E X y))

(* Note: Elb proves Dlb for some bound B', but we want tight control over when B' = 0 *)
  protectedDefinition is_bounded.mk {R : Ring} {I : AddAbGroup} {X : exact_couple R I}
  (B B' B'' : I -> ℕ)
  (Dub : forall (x : I) (s : ℕ), B x ≤ s -> is_contr (D X ((deg (i X))^[s] x)))
  (Dlb : forall (x : I) (s : ℕ), B' x ≤ s -> is_surjective (i X (((deg (i X))^-1ᵉ^[s + 1] x))))
  (Elb : forall (x : I) (s : ℕ), B'' x ≤ s -> is_contr (E X ((deg (i X))^-1ᵉ^[s] x))) : is_bounded X.
Proof.
  apply is_bounded.mk' (fun x => max (B x) (B'' x)) B',
  { intro x y s p h, induction p, exact Dub (le.trans !le_max_left h) },
  { exact abstract begin intro x y z s p q h, induction p, induction q,
  refine transport (fun x => is_surjective (i X x)) _ (Dlb h),
  rewrite [-iterate_succ], apply iterate_left_inv end end },
  { intro x y s p h, induction p, exact Elb (le.trans !le_max_right h) }
Defined.

  open is_bounded
Definition is_bounded_reindex {R : Ring} {I J : AddAbGroup}
  (e : AddGroup_of_AddAbGroup J <~>g AddGroup_of_AddAbGroup I)
  {X : exact_couple R I} (HH : is_bounded X) : is_bounded (exact_couple_reindex e X).
Proof.
  apply is_bounded.mk' (B HH o e) (B' HH o e),
  { intros x y s p h, refine Dub HH _ h,
  refine (iterate_hsquare e _ s x)^-1 @ ap e p, intro x,
  exact to_right_inv (group.equiv_of_isomorphism e) _ },
  { intros x y z s p q h, refine Dlb HH _ _ h,
  refine (iterate_hsquare e _ s y)^-1 @ ap e q, intro x,
  exact to_right_inv (group.equiv_of_isomorphism e) _ },
  { intro x y s p h, refine Elb HH _ h,
  refine (iterate_hsquare e _ s x)^-1 @ ap e p, intro x,
  exact to_right_inv (group.equiv_of_isomorphism e) _ },

Defined.

  namespace convergence_Definition
  section

  parameters {R : Ring} {I : AddAbGroup} (X : exact_couple R I) (HH : is_bounded X)

  local abbreviation B . B HH
  local abbreviation B' . B' HH
  local abbreviation Dub . Dub HH
  local abbreviation Dlb . Dlb HH
  local abbreviation Elb . Elb HH

  (* We start counting pages at 0, which corresponds to what is usually called the second page *)
Definition page (r : ℕ) : exact_couple R I.
  iterate derived_couple r X

Definition is_contr_E (r : ℕ) (x : I) (h : is_contr (E X x)) :
  is_contr (E (page r) x).
  by induction r with r IH; exact h; exact is_contr_E' (page r) IH

Definition is_contr_D (r : ℕ) (x : I) (h : is_contr (D X x)) :
  is_contr (D (page r) x).
  by induction r with r IH; exact h; exact is_contr_D' (page r) IH

Definition deg_i (r : ℕ) : deg (i (page r)) == deg (i X).
Proof.
  induction r with r IH,
  { reflexivity },
  { exact IH }
Defined.

Definition deg_k (r : ℕ) : deg (k (page r)) == deg (k X).
Proof.
  induction r with r IH,
  { reflexivity },
  { exact IH }
Defined.

Definition deg_j (r : ℕ) :
  deg (j (page r)) == deg (j X) o iterate (deg (i X))^-1 r.
Proof.
  induction r with r IH,
  { reflexivity },
  { refine hwhisker_left (deg (j (page r)))
  (to_inv_homotopy_inv (deg_i r)) @hty _,
  refine hwhisker_right _ IH @hty _,
  apply hwhisker_left, symmetry, apply iterate_succ }
Defined.

Definition deg_j_inv (r : ℕ) :
  (deg (j (page r)))^-1 == iterate (deg (i X)) r o (deg (j X))^-1.
  have H : deg (j (page r)) == iterate_equiv (deg (i X))^-1ᵉ r @e deg (j X), from deg_j r,
  fun x => to_inv_homotopy_inv H x @ iterate_inv (deg (i X))^-1ᵉ r ((deg (j X))^-1 x)

Definition deg_dr (r : ℕ) :
  deg (d (page r)) == deg (j X) o iterate (deg (i X))^-1 r o deg (k X).
  compose2 (deg_j r) (deg_k r)

Definition deg_dr_inv (r : ℕ) :
  (deg (d (page r)))^-1 == (deg (k X))^-1 o iterate (deg (i X)) r o (deg (j X))^-1.
  compose2 (to_inv_homotopy_inv (deg_k r)) (deg_j_inv r)

  (*Definition E_isomorphism' {x : I} {r₁ r₂ : ℕ} (H : r₁ ≤ r₂) *)
  (*   (H1 : forall (r), r₁ ≤ r -> r < r₂ -> is_contr (E X ((deg (d (page r)))^-1ᵉ x))) *)
  (*   (H2 : forall (r), r₁ ≤ r -> r < r₂ -> is_contr (E X (deg (d (page r)) x))) : *)
  (*   E (page r₂) x <~>lm E (page r₁) x . *)
  (* begin *)
  (*   assert H2 : forall (r), r₁ ≤ r -> r ≤ r₂ -> E (page r) x <~>lm E (page r₁) x, *)
  (*   { intro r Hr₁ Hr₂, *)
  (*     induction Hr₁ with r Hr₁ IH, reflexivity, *)
  (*     let Hr₂' . le_of_succ_le Hr₂, *)
  (*     exact E'_isomorphism (page r) (is_contr_E r _ (H1 Hr₁ Hr₂)) (is_contr_E r _ (H2 Hr₁ Hr₂)) *)
  (*       @lm IH Hr₂' }, *)
  (*   exact H2 H (le.refl _) *)
  (* end *)

  (*Definition E_isomorphism0' {x : I} {r : ℕ} *)
  (*   (H1 : forall r, is_contr (E X ((deg (d (page r)))^-1ᵉ x))) *)
  (*   (H2 : forall r, is_contr (E X (deg (d (page r)) x))) : E (page r) x <~>lm E X x . *)
  (* E_isomorphism' (zero_le r) _ _ *)

  parameter {X}

Definition deg_iterate_ik_commute (n : ℕ) :
  hsquare (deg (k X)) (deg (k X)) ((deg (i X))^[n]) ((deg (i X))^[n]).
  iterate_commute n (deg_commute (k X) (i X))

Definition deg_iterate_ij_commute (n : ℕ) :
  hsquare (deg (j X)) (deg (j X)) ((deg (i X))^-1ᵉ^[n]) ((deg (i X))^-1ᵉ^[n]).
  iterate_commute n (deg_commute (j X) (i X))^-1ʰᵗʸᵛ

Definition B2 (x : I) : ℕ . max (B (deg (k X) x)) (B ((deg (j X))^-1 x))
Definition Eub (x y : I) (s : ℕ) (p : (deg (i X))^[s] x = y) (h : B2 x ≤ s) :
  is_contr (E X y).
Proof.
  induction p,
  refine @(is_contr_middle_of_is_exact (exact_couple.jk X (right_inv (deg (j X)) _) idp)) _ _ _,
  exact Dub (iterate_commute s (deg_commute (j X) (i X))^-1ʰᵗʸʰ x) (le.trans !le_max_right h),
  exact Dub (deg_iterate_ik_commute s x) (le.trans !le_max_left h)
Defined.

Definition B3 (x : I) : ℕ.
  max (B (deg (j X) (deg (k X) x))) (B2 ((deg (k X))^-1 ((deg (j X))^-1 x)))

Definition Estable {x : I} {r : ℕ} (H : B3 x ≤ r) :
  E (page (r + 1)) x <~>lm E (page r) x.
Proof.
  change homology (d (page r) x) (d (page r) ← x) <~>lm E (page r) x,
  apply homology_isomorphism: apply is_contr_E,
  exact Eub (hhinverse (deg_iterate_ik_commute r) _ @ (deg_dr_inv r x)^-1)
  (le.trans !le_max_right H),
  exact Elb (deg_iterate_ij_commute r _ @ (deg_dr r x)^-1)
  (le.trans !le_max_left H)
Defined.

Definition is_surjective_i {x y z : I} {r s : ℕ} (H : B' z ≤ s + r)
  (p : deg (i (page r)) x = y) (q : iterate (deg (i X)) s y = z) :
  is_surjective (i (page r) ↘ p).
Proof.
  revert x y z s H p q, induction r with r IH: intro x y z s H p q,
  { exact Dlb p q H },
  { change is_surjective (i' (page r) ↘ p),
  apply is_surjective_i', intro z' q',
  refine IH _ _ _ _ (le.trans H (le_of_eq (succ_add s r)^-1)) _ _,
  refine !iterate_succ @ ap ((deg (i X))^[s]) _ @ q,
  exact !deg_i^-1 @ p }
Defined.

Definition Dstable {x : I} {r : ℕ} (H : B' x ≤ r) :
  D (page (r + 1)) x <~>lm D (page r) x.
Proof.
  change image_module (i (page r) ← x) <~>lm D (page r) x,
  refine image_module_isomorphism (i (page r) ← x)
  (is_surjective_i (le.trans H (le_of_eq !zero_add^-1)) _ _),
  reflexivity
Defined.

  (* the infinity pages of E and D *)
Definition Einf : graded_module R I.
  fun x => E (page (B3 x)) x

Definition Dinf : graded_module R I.
  fun x => D (page (B' x)) x

Definition Einfstable {x y : I} {r : ℕ} (Hr : B3 y ≤ r) (p : x = y) : Einf y <~>lm E (page r) x.
  by symmetry; induction p; induction Hr with r Hr IH; reflexivity; exact Estable Hr @lm IH

Definition Dinfstable {x y : I} {r : ℕ} (Hr : B' y ≤ r) (p : x = y) : Dinf y <~>lm D (page r) x.
  by symmetry; induction p; induction Hr with r Hr IH; reflexivity; exact Dstable Hr @lm IH

  (*Definition Einf_isomorphism' {x : I} (r₁ : ℕ) *)
  (*   (H1 : forall (r), r₁ ≤ r -> is_contr (E X ((deg (d (page r)))^-1ᵉ x))) *)
  (*   (H2 : forall (r), r₁ ≤ r -> is_contr (E X (deg (d (page r)) x))) : *)
  (*   Einf x <~>lm E (page r₁) x . *)
  (* begin *)
  (*   cases le.total r₁ (B3 x) with Hr Hr, *)
  (*   exact E_isomorphism' Hr (fun r Hr₁ Hr₂ => H1 Hr₁) (fun r Hr₁ Hr₂ => H2 Hr₁), *)
  (*   exact Einfstable Hr idp *)
  (* end *)

  (*Definition Einf_isomorphism0' {x : I} *)
  (*   (H1 : forall (r), is_contr (E X ((deg (d (page r)))^-1ᵉ x))) *)
  (*   (H2 : forall (r), is_contr (E X (deg (d (page r)) x))) : *)
  (*   Einf x <~>lm E X x . *)
  (* E_isomorphism0' _ _ *)

  parameters (x : I)

Definition rb (n : ℕ) : ℕ.
  max (max (B (deg (j X) (deg (k X) x)) + n + 1) (B3 ((deg (i X))^[n] x)))
  (max (B' (deg (k X) ((deg (i X))^[n] x)))
  (max (B' (deg (k X) ((deg (i X))^[n+1] x))) (B ((deg (j X))^-1 ((deg (i X))^[n] x)))))

  lemma rb0 (n : ℕ) : rb n ≥ n + 1.
  ge.trans !le_max_left (ge.trans !le_max_left !le_add_left)
  lemma rb1 (n : ℕ) : B (deg (j X) (deg (k X) x)) ≤ rb n - (n + 1).
  nat.le_sub_of_add_le (le.trans !le_max_left !le_max_left)
  lemma rb2 (n : ℕ) : B3 ((deg (i X))^[n] x) ≤ rb n.
  le.trans !le_max_right !le_max_left
  lemma rb3 (n : ℕ) : B' (deg (k X) ((deg (i X))^[n] x)) ≤ rb n.
  le.trans !le_max_left !le_max_right
  lemma rb4 (n : ℕ) : B' (deg (k X) ((deg (i X))^[n+1] x)) ≤ rb n.
  le.trans (le.trans !le_max_left !le_max_right) !le_max_right
  lemma rb5 (n : ℕ) : B ((deg (j X))^-1 ((deg (i X))^[n] x)) ≤ rb n.
  le.trans (le.trans !le_max_right !le_max_right) !le_max_right

Definition Einfdiag : graded_module R ℕ.
  fun n => Einf ((deg (i X))^[n] x)

Definition Dinfdiag : graded_module R ℕ.
  fun n => Dinf (deg (k X) ((deg (i X))^[n] x))

Definition short_exact_mod_page_r (n : ℕ) : short_exact_mod
  (E (page (rb n)) ((deg (i X))^[n] x))
  (D (page (rb n)) (deg (k (page (rb n))) ((deg (i X))^[n] x)))
  (D (page (rb n)) (deg (i (page (rb n))) (deg (k (page (rb n))) ((deg (i X))^[n] x)))).
Proof.
  fapply short_exact_mod_of_is_exact,
  { exact j (page (rb n)) ← ((deg (i X))^[n] x) },
  { exact k (page (rb n)) ((deg (i X))^[n] x) },
  { exact i (page (rb n)) (deg (k (page (rb n))) ((deg (i X))^[n] x)) },
  { exact j (page (rb n)) _ },
  { apply is_contr_D, refine Dub !deg_j_inv^-1 (rb5 n) },
  { apply is_contr_E, refine Elb _ (rb1 n),
  refine !deg_iterate_ij_commute @ _,
  refine ap (deg (j X)) _ @ !deg_j^-1,
  refine iterate_sub _ !rb0 _ @ _, apply ap (_^[rb n]),
  exact ap (deg (i X)) (!deg_iterate_ik_commute @ !deg_k^-1) @ !deg_i^-1 },
  { apply jk (page (rb n)) },
  { apply ki (page (rb n)) },
  { apply ij (page (rb n)) }
Defined.

Definition short_exact_mod_infpage (n : ℕ) :
  short_exact_mod (Einfdiag n) (Dinfdiag n) (Dinfdiag (n+1)).
Proof.
  refine short_exact_mod_isomorphism _ _ _ (short_exact_mod_page_r n),
  { exact Einfstable !rb2 idp },
  { exact Dinfstable !rb3 !deg_k },
  { exact Dinfstable !rb4 (!deg_i @ ap (deg (i X)) !deg_k @ deg_commute (k X) (i X) _) }
Defined.

Definition Dinfdiag0 (bound_zero : B' (deg (k X) x) = 0) : Dinfdiag 0 <~>lm D X (deg (k X) x).
  Dinfstable (le_of_eq bound_zero) idp

  lemma Dinfdiag_stable {s : ℕ} (h : B (deg (k X) x) ≤ s) : is_contr (Dinfdiag s).
  is_contr_D _ _ (Dub !deg_iterate_ik_commute h)

  (* some useful immediate properties *)

Definition short_exact_mod_infpage0 (bound_zero : B' (deg (k X) x) = 0) :
  short_exact_mod (Einfdiag 0) (D X (deg (k X) x)) (Dinfdiag 1).
Proof.
  refine short_exact_mod_isomorphism _ _ _ (short_exact_mod_infpage 0),
  { reflexivity },
  { exact (Dinfdiag0 bound_zero)^-1ˡᵐ },
  { reflexivity }
Defined.

  (* the convergenceDefinition is the following result *)
Definition is_built_from_infpage (bound_zero : B' (deg (k X) x) = 0) :
  is_built_from (D X (deg (k X) x)) Einfdiag.
  is_built_from.mk Dinfdiag short_exact_mod_infpage (Dinfdiag0 bound_zero) (B (deg (k X) x))
  (fun s => Dinfdiag_stable)

Defined.

Definition deg_dr_reindex {R : Ring} {I J : AddAbGroup}
  (e : AddGroup_of_AddAbGroup J <~>g AddGroup_of_AddAbGroup I) (X : exact_couple R I)
  (r : ℕ) : deg (d (page (exact_couple_reindex e X) r)) ~
  e^-1ᵍ o deg (d (page X r)) o e.
Proof.
  intro x, refine !deg_dr @ _ @ ap e^-1ᵍ !deg_dr^-1,
  apply ap (e^-1ᵍ o deg (j X)),
  note z . @iterate_hsquare _ _ (deg (i (exact_couple_reindex e X)))^-1ᵉ (deg (i X))^-1ᵉ e
  (fun x => proof to_right_inv (group.equiv_of_isomorphism e) _ qed)^-1ʰᵗʸʰ r,
  refine z _ @ _, apply ap ((deg (i X))^-1ᵉ^[r]),
  exact to_right_inv (group.equiv_of_isomorphism e) _
Defined.

Defined. convergence_Definition

  open int group prod convergence_Definition prod.ops

  local attribute [coercion] AddAbGroup_of_Ring
Definition Z2 : AddAbGroup . rℤ \*aa rℤ

  structure convergent_exact_couple.{u v w} {R : Ring} (E' : ℤ -> ℤ -> LeftModule.{u v} R)
  (Dinf : ℤ -> LeftModule.{u w} R) : Type.{max u (v+1) (w+1)}.
  (X : exact_couple.{u 0 w v} R Z2)
  (HH : is_bounded X)
  (st : ℤ -> Z2)
  (HB : forall (n : ℤ), is_bounded.B' HH (deg (k X) (st n)) = 0)
  (e : forall (x : Z2), exact_couple.E X x <~>lm E' x.1 x.2)
  (f : forall (n : ℤ), exact_couple.D X (deg (k X) (st n)) <~>lm Dinf n)
  (deg_d : ℕ -> Z2)
  (deg_d_eq0 : forall (r : ℕ), deg (d (page X r)) 0 = deg_d r)

  infix ` ⟹ `:25 . convergent_exact_couple (* todo: maybe this should define convergent_spectral_sequence *)

Definition convergent_exact_couple_g (E' : ℤ -> ℤ -> AbGroup) (Dinf : ℤ -> AbGroup) : Type.
  (fun n s => LeftModule_int_of_AbGroup (E' n s)) ⟹ (fun n => LeftModule_int_of_AbGroup (Dinf n))

  infix ` ⟹ᵍ `:25 . convergent_exact_couple_g

  section exact_couple
  open convergent_exact_couple
  parameters {R : Ring} {E' : ℤ -> ℤ -> LeftModule R} {Dinf : ℤ -> LeftModule R} (c : E' ⟹ Dinf)
  local abbreviation X . X c
  local abbreviation i . i X
  local abbreviation HH . HH c
  local abbreviation st . st c
  local abbreviation Dinfdiag (n : ℤ) (k : ℕ) . Dinfdiag HH (st n) k
  local abbreviation Einfdiag (n : ℤ) (k : ℕ) . Einfdiag HH (st n) k

Definition deg_d_eq (r : ℕ) (ns : Z2) : (deg (d (page X r))) ns = ns + deg_d c r.
  !deg_eq @ ap (fun x => _ + x) (deg_d_eq0 c r)

Definition deg_d_inv_eq (r : ℕ) (ns : Z2) :
  (deg (d (page X r)))^-1ᵉ ns = ns - deg_d c r.
  inv_eq_of_eq (!deg_d_eq @ proof !neg_add_cancel_right qed)^-1

Definition convergent_exact_couple_isomorphism {E'' : ℤ -> ℤ -> LeftModule R} {Dinf' : graded_module R ℤ}
  (e' : forall n s, E' n s <~>lm E'' n s) (f' : forall n, Dinf n <~>lm Dinf' n) : E'' ⟹ Dinf'.
  convergent_exact_couple.mk X HH st (HB c)
Proof. intro x, induction x with n s, exact e c (n, s) @lm e' n s end
  (fun n => f c n @lm f' n) (deg_d c) (deg_d_eq0 c)

  include c
Definition convergent_exact_couple_reindex (i : agℤ \*ag agℤ <~>g agℤ \*ag agℤ) :
  (fun p q => E' (i (p, q)).1 (i (p, q)).2) ⟹ Dinf.
Proof.
  fapply convergent_exact_couple.mk (exact_couple_reindex i X) (is_bounded_reindex i HH),
  { exact fun n => i^-1ᵍ (st n) },
  { intro n, refine ap (B' HH) _ @ HB c n,
  refine to_right_inv (group.equiv_of_isomorphism i) _ @ _,
  apply ap (deg (k X)), exact to_right_inv (group.equiv_of_isomorphism i) _ },
  { intro x, induction x with p q, exact e c (i (p, q)) },
  { intro n, refine _ @lm f c n, refine isomorphism_of_eq (ap (D X) _),
  refine to_right_inv (group.equiv_of_isomorphism i) _ @ _,
  apply ap (deg (k X)), exact to_right_inv (group.equiv_of_isomorphism i) _ },
  { exact fun n => i^-1ᵍ (deg_d c n) },
  { intro r, esimp, refine !deg_dr_reindex @ ap i^-1ᵍ (ap (deg (d _)) (group.to_respect_zero i) @
  deg_d_eq0 c r) }
Defined.

Definition convergent_exact_couple_negate_abutment : E' ⟹ (fun n => Dinf (-n)).
  convergent_exact_couple.mk X HH (st o neg) (fun n => HB c (-n)) (e c) (fun n => f c (-n))
  (deg_d c) (deg_d_eq0 c)
  omit c

Definition is_built_from_of_convergent_exact_couple (n : ℤ) :
  is_built_from (Dinf n) (Einfdiag n).
  is_built_from_isomorphism_left (f c n) (is_built_from_infpage HH (st n) (HB c n))

Definition is_contr_convergent_exact_couple_precise (n : ℤ)
  (H : forall (n : ℤ) (l : ℕ), is_contr (E' ((deg i)^[l] (st n)).1 ((deg i)^[l] (st n)).2)) :
  is_contr (Dinf n).
Proof.
  assert H2 : forall (l : ℕ), is_contr (Einfdiag n l),
  { intro l, apply is_contr_E,
  refine is_trunc_equiv_closed_rev -2 (equiv_of_isomorphism (e c _)) (H n l) },
  exact is_contr_total (is_built_from_of_convergent_exact_couple n) H2
Defined.

Definition is_contr_convergent_exact_couple (n : ℤ) (H : forall (n s : ℤ), is_contr (E' n s)) :
  is_contr (Dinf n).
  is_contr_convergent_exact_couple_precise n (fun n s => !H)

  (*Definition E_isomorphism {r₁ r₂ : ℕ} {n s : ℤ} (H : r₁ ≤ r₂) *)
  (*   (H1 : forall (r), r₁ ≤ r -> r < r₂ -> is_contr (E X ((n, s) - deg_d c r))) *)
  (*   (H2 : forall (r), r₁ ≤ r -> r < r₂ -> is_contr (E X ((n, s) + deg_d c r))) : *)
  (*   E (page X r₂) (n, s) <~>lm E (page X r₁) (n, s) . *)
  (* E_isomorphism' X H *)
  (*   (fun r Hr₁ Hr₂ => transport (is_contr o E X) (deg_d_inv_eq r (n, s))^-1ᵖ (H1 Hr₁ Hr₂)) *)
  (*   (fun r Hr₁ Hr₂ => transport (is_contr o E X) (deg_d_eq r (n, s))^-1ᵖ (H2 Hr₁ Hr₂)) *)

  (*Definition E_isomorphism0 {r : ℕ} {n s : ℤ} (H1 : forall r, is_contr (E X ((n, s) - deg_d c r))) *)
  (*   (H2 : forall r, is_contr (E X ((n, s) + deg_d c r))) : E (page X r) (n, s) <~>lm E' n s . *)
  (* E_isomorphism (zero_le r) _ _ @lm e c (n, s) *)

  (*Definition Einf_isomorphism (r₁ : ℕ) {n s : ℤ} *)
  (*   (H1 : forall (r), r₁ ≤ r -> is_contr (E X ((n,s) - deg_d c r))) *)
  (*   (H2 : forall (r), r₁ ≤ r -> is_contr (E X ((n,s) + deg_d c r))) : *)
  (*   Einf HH (n, s) <~>lm E (page X r₁) (n, s) . *)
  (* Einf_isomorphism' HH r₁ (fun r Hr₁ => transport (is_contr o E X) (deg_d_inv_eq r (n, s))^-1ᵖ (H1 Hr₁)) *)
  (*                        (fun r Hr₁ => transport (is_contr o E X) (deg_d_eq r (n, s))^-1ᵖ (H2 Hr₁)) *)

  (*Definition Einf_isomorphism0 {n s : ℤ} *)
  (*   (H1 : forall (r), is_contr (E X ((n,s) - deg_d c r))) *)
  (*   (H2 : forall (r), is_contr (E X ((n,s) + deg_d c r))) : *)
  (*   Einf HH (n, s) <~>lm E' n s . *)
  (* E_isomorphism0 _ _ *)

Defined. exact_couple

  variables {E' : ℤ -> ℤ -> AbGroup} {Dinf : ℤ -> AbGroup}
Definition convergent_exact_couple_g_isomorphism {E'' : ℤ -> ℤ -> AbGroup}
  {Dinf' : ℤ -> AbGroup} (c : E' ⟹ᵍ Dinf)
  (e' : forall n s, E' n s <~>g E'' n s) (f' : forall n, Dinf n <~>g Dinf' n) : E'' ⟹ᵍ Dinf'.
  convergent_exact_couple_isomorphism c (fun n s => lm_iso_int.mk (e' n s)) (fun n => lm_iso_int.mk (f' n))

Defined. exact_couple
open exact_couple
namespace pointed

  open pointed int group is_trunc trunc is_conn

Definition homotopy_group_conn_nat (n : ℕ) (A : pType[1]) : AbGroup.
  AbGroup.mk (forall [n] A) (ab_group_homotopy_group_of_is_conn n A)

Definition homotopy_group_conn : forall (n : ℤ) (A : pType[1]), AbGroup
  | (of_nat n) A . homotopy_group_conn_nat n A
  | (-[1+ n])  A . trivial_ab_group_lift

  notation `forall c[`:95 n:0 `]`:0 . homotopy_group_conn n

Definition homotopy_group_conn_nat_functor (n : ℕ) {A B : pType[1]} (f : A ->* B) :
  homotopy_group_conn_nat n A ->g homotopy_group_conn_nat n B.
Proof.
  cases n with n, { apply group.trivial_homomorphism },
  cases n with n, { apply group.trivial_homomorphism },
  exact forall ->g[n+2] f
Defined.

Definition homotopy_group_conn_functor :
  forall (n : ℤ) {A B : pType[1]} (f : A ->* B), forall c[n] A ->g forall c[n] B
  | (of_nat n) A B f . homotopy_group_conn_nat_functor n f
  | (-[1+ n])  A B f . trivial_homomorphism _ _

  notation `forall ->c[`:95 n:0 `]`:0 . homotopy_group_conn_functor n

  section
  open prod prod.ops fiber
  parameters {A : ℤ -> pType[1]} (f : forall (n : ℤ), A n ->* A (n - 1)) [Hf : forall n, is_conn_fun 1 (f n)]
  include Hf
  local abbreviation I . Z2

  (*Definition D_sequence : graded_module rℤ I . *)
  (* fun v => LeftModule_int_of_AbGroup (forall c[v.2] (A (v.1))) *)

  (*Definition E_sequence : graded_module rℤ I . *)
  (* fun v => LeftModule_int_of_AbGroup (forall c[v.2] (pconntype.mk (pfiber (f (v.1))) !Hf (point _))) *)

  (* first need LES of these connected homotopy groups *)

  (*Definition exact_couple_sequence : exact_couple rℤ I . *)
  (* exact_couple.mk D_sequence E_sequence sorry sorry sorry sorry sorry sorry *)

Defined.


Defined. pointed

namespace spectrum
  open pointed int group is_trunc trunc is_conn prod prod.ops group fin chain_complex
  section

  parameters {A : ℤ -> spectrum} (f : forall (s : ℤ), A s ->ₛ A (s - 1))

  local abbreviation I . Z2

Definition D_sequence : graded_module rℤ I.
  fun v => LeftModule_int_of_AbGroup (forall ₛ[v.1] (A (v.2)))

Definition E_sequence : graded_module rℤ I.
  fun v => LeftModule_int_of_AbGroup (forall ₛ[v.1] (sfiber (f (v.2))))

  include f

Definition i_sequence : D_sequence ->gm D_sequence.
Proof.
  fapply graded_hom.mk, exact (prod_equiv_prod erfl (add_right_action (- 1))),
  { intro i, exact pair_eq !add_zero^-1 idp },
  intro v,
  apply lm_hom_int.mk, esimp,
  rexact forall ₛ->[v.1] (f v.2)
Defined.

Definition deg_j_seq_inv : I <~> I.
  prod_equiv_prod (add_right_action 1) (add_right_action (- 1))

Definition fn_j_sequence (x : I) :
  D_sequence (deg_j_seq_inv x) ->lm E_sequence x.
Proof.
  induction x with n s,
  apply lm_hom_int.mk, esimp,
  rexact shomotopy_groups_fun (f s) (n => 2)
Defined.

Definition j_sequence : D_sequence ->gm E_sequence.
  graded_hom.mk_out deg_j_seq_inv^-1ᵉ (fun i => idp) fn_j_sequence

Definition k_sequence : E_sequence ->gm D_sequence.
Proof.
  fapply graded_hom.mk erfl deg_eq_id,
  intro v, induction v with n s,
  apply lm_hom_int.mk, esimp,
  exact forall ₛ->[n] (spoint (f s))
Defined.

  lemma ij_sequence : is_exact_gmod i_sequence j_sequence.
Proof.
  intro x y z p q,
  revert y z q p,
  refine eq.rec_right_inv (deg j_sequence) _,
  intro y, induction x with n s, induction y with m t,
  refine equiv_rect !pair_eq_pair_equiv^-1ᵉ _ _,
  intro pq, esimp at pq, induction pq with p q,
  revert t q, refine eq.rec_equiv (add_right_action (- 1)) _,
  induction p using eq.rec_symm,
  apply is_exact_homotopy homotopy.rfl,
  { symmetry, exact graded_hom_mk_out_destruct deg_j_seq_inv^-1ᵉ (fun i => idp) fn_j_sequence },
  rexact is_exact_of_is_exact_at (is_exact_LES_of_shomotopy_groups (f s) (m, 2)),
Defined.

  lemma jk_sequence : is_exact_gmod j_sequence k_sequence.
Proof.
  intro x y z p q, induction q,
  revert x y p, refine eq.rec_right_inv (deg j_sequence) _,
  intro x, induction x with n s,
  apply is_exact_homotopy,
  { symmetry, exact graded_hom_mk_out_destruct deg_j_seq_inv^-1ᵉ (fun i => idp) fn_j_sequence },
  { reflexivity },
  rexact is_exact_of_is_exact_at (is_exact_LES_of_shomotopy_groups (f s) (n, 1)),
Defined.

  lemma ki_sequence : is_exact_gmod k_sequence i_sequence.
Proof.
  intro x y z p q, induction p, induction q, induction x with n s,
  rexact is_exact_of_is_exact_at (is_exact_LES_of_shomotopy_groups (f s) (n, 0)),
Defined.

Definition exact_couple_sequence : exact_couple rℤ I.
  exact_couple.mk D_sequence E_sequence i_sequence j_sequence k_sequence
  ij_sequence jk_sequence ki_sequence

  open int
  parameters (ub : ℤ -> ℤ) (lb : ℤ -> ℤ)
  (Aub : forall (s n : ℤ), s ≥ ub n + 1 -> is_equiv (forall ₛ->[n] (f s)))
  (Alb : forall (s n : ℤ), s ≤ lb n -> is_contr (forall ₛ[n] (A s)))

Definition B : I -> ℕ
  | (n, s) . max0 (s - lb n)

Definition B' : I -> ℕ
  | (n, s) . max0 (ub n - s)

Definition B'' : I -> ℕ
  | (n, s) . max0 (max (ub n + 1 - s) (ub (n+1) + 1 - s))

  lemma iterate_deg_i (n s : ℤ) (m : ℕ) : (deg i_sequence)^[m] (n, s) = (n, s - m).
Proof.
  induction m with m IH,
  { exact prod_eq idp !sub_zero^-1 },
  { exact ap (deg i_sequence) IH @ (prod_eq idp !sub_sub) }
Defined.

  lemma iterate_deg_i_inv (n s : ℤ) (m : ℕ) : (deg i_sequence)^-1ᵉ^[m] (n, s) = (n, s + m).
Proof.
  induction m with m IH,
  { exact prod_eq idp !add_zero^-1 },
  { exact ap (deg i_sequence)^-1ᵉ IH @ (prod_eq idp !add.assoc) }
Defined.

  include Aub Alb
  lemma Dub (x : I) (t : ℕ) (h : B x ≤ t) : is_contr (D_sequence ((deg i_sequence)^[t] x)).
Proof.
  apply Alb, induction x with n s, rewrite [iterate_deg_i],
  apply sub_le_of_sub_le,
  exact le_of_max0_le h,
Defined.

  lemma Dlb (x : I) (t : ℕ) (h : B' x ≤ t) :
  is_surjective (i_sequence ((deg i_sequence)^-1ᵉ^[t+1] x)).
Proof.
  apply is_surjective_of_is_equiv,
  apply Aub, induction x with n s,
  rewrite [iterate_deg_i_inv, ▸*, of_nat_add, -add.assoc],
  apply add_le_add_right,
  apply le_add_of_sub_left_le,
  exact le_of_max0_le h
Defined.

  lemma Elb (x : I) (t : ℕ) (h : B'' x ≤ t) : is_contr (E_sequence ((deg i_sequence)^-1ᵉ^[t] x)).
Proof.
  induction x with n s,
  rewrite [iterate_deg_i_inv, ▸*],
  apply is_contr_shomotopy_group_sfiber_of_is_equiv,
  apply Aub, apply le_add_of_sub_left_le, apply le_of_max0_le, refine le.trans _ h,
  apply max0_monotone, apply le_max_left,
  apply Aub, apply le_add_of_sub_left_le, apply le_of_max0_le, refine le.trans _ h,
  apply max0_monotone, apply le_max_right
Defined.

Definition is_bounded_sequence : is_bounded exact_couple_sequence.
  is_bounded.mk B B' B'' Dub Dlb Elb
  (* (by intro x; reflexivity) *)
  (* begin *)
  (*   intro x, induction x with n s, apply pair_eq, esimp, esimp, esimp [j_sequence, i_sequence], *)
  (*   refine !add.assoc @ ap (add s) !add.comm @ !add.assoc^-1, *)
  (* end *)

Definition convergent_exact_couple_sequence : (fun n s => forall , forall ₛ[n] (A (ub n))).
Proof.
  fapply convergent_exact_couple.mk,
  { exact exact_couple_sequence },
  { exact is_bounded_sequence },
  { exact fun n => (n, ub n) },
  { intro n, change max0 (ub n - ub n) = 0, exact ap max0 (sub_self (ub n)) },
  { intro ns, reflexivity },
  { intro n, reflexivity },
  { intro r, exact (- 1, r + 1) },
  { intro r, refine !convergence_Definition.deg_dr @ _,
  refine ap (deg j_sequence) !iterate_deg_i_inv @ _,
  exact prod_eq idp !zero_add }
Defined.

Defined.

(* Uncomment the next line to see that the proof uses univalence, but that there are no holes *)
--('sorry') in the proof:

(* print axioms is_bounded_sequence *)

(* It depends on univalence in an essential way. The reason is that the long exact sequence *)
(* of homotopy groups already depends on univalence. Namely, in that proof we need to show that if f *)
(* : A -> B and g : B -> C are exact at B, then ∥A∥₀ -> ∥B∥₀ -> ∥C∥₀ is exact at ∥B∥₀. For this we need *)
(* that the equality |b|₀ = |b'|₀ is equivalent to ∥b = b'∥₋₁, which requires univalence. *)
Defined. spectrum
