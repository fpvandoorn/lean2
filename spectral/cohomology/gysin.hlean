(* the construction of the Gysin sequence using the Serre spectral sequence *)

import .serre

open eq pointed is_trunc is_conn is_equiv equiv sphere fiber chain_complex left_module spectrum nat
  prod nat int algebra function spectral_sequence fin group

namespace cohomology
universe variable u
(*
  Given a pointed map E ->* B with as fiber the sphere S^{n+1} and an abelian group A.
  The only nontrivial differentials in the spectral sequence of this map are the following
  differentials on page n:
  d_m = d_(m-1,n+1)^n : E_(m-1,n+1)^n -> E_(m+n+1,0)^n
  Note that ker d_m = E_(m-1,n+1)^∞ and coker d_m = E_(m+n+1,0)^∞.
  Each diagonal on the ∞-page has at most two nontrivial groups, which means that
  coker d_{m-1} and ker d_m are the only two nontrivial groups building up D_{m+n}^∞,
  where D^∞ is the abutment of the spectral sequence.
  This gives the short exact sequences:
  coker d_{m-1} -> D_{m+n}^∞  -> ker d_m
  We can splice these SESs together to get a LES
  ... E_(m+n,0)^n -> D_{m+n}^∞ -> E_(m-1,n+1)^n -> E_(m+n+1,0)^n -> D_{m+n+1}^∞ ...
  Now we have
  E_(p,q)^n = E_(p,q)^0 = H^p(B; H^q(S^{n+1}; A)) = H^p(B; A) if q = n+1 or q = 0
  and
  D_{n}^∞ = H^n(E; A)
  This gives the Gysin sequence
  ... H^{m+n}(B; A) -> H^{m+n}(E; A) -> H^{m-1}(B; A) -> H^{m+n+1}(B; A) -> H^{m+n+1}(E; A) ...
*)


Definition gysin_trivial_Epage {E B : pType.{u}} {n : ℕ} (HB : is_conn 1 B) (f : E ->* B)
  (e : pfiber f <~>* sphere (n+1)) (A : AbGroup) (r : ℕ) (p q : ℤ) (hq : q ≠ 0)
  (hq' : q ≠ of_nat (n+1)):
  is_contr (convergent_spectral_sequence.E (serre_spectral_sequence_map_of_is_conn (point _) f
  (EM_spectrum A) 0 (is_strunc_EM_spectrum A) HB) r (p, q)).
Proof.
  intros, apply is_contr_E, apply is_contr_ordinary_cohomology, esimp,
  refine is_contr_equiv_closed_rev _ (unreduced_ordinary_cohomology_sphere_of_neq A hq' hq),
  apply group.equiv_of_isomorphism, apply unreduced_ordinary_cohomology_isomorphism, exact e^-1ᵉ*
Defined.

Definition gysin_trivial_Epage2 {E B : pType.{u}} {n : ℕ} (HB : is_conn 1 B) (f : E ->* B)
  (e : pfiber f <~>* sphere (n+1)) (A : AbGroup) (r : ℕ) (p q : ℤ) (hq : q > n+1) :
  is_contr (convergent_spectral_sequence.E (serre_spectral_sequence_map_of_is_conn (point _) f
  (EM_spectrum A) 0 (is_strunc_EM_spectrum A) HB) r (p, q)).
Proof.
  intros, apply gysin_trivial_Epage HB f e A r p q,
  { intro h, subst h, apply not_lt_zero (n+1), exact lt_of_of_nat_lt_of_nat hq },
  { intro h, subst h, exact lt.irrefl _ hq }
Defined.

Definition gysin_sequence' {E B : pType.{u}} {n : ℕ} (HB : is_conn 1 B) (f : E ->* B)
  (e : pfiber f <~>* sphere (n+1)) (A : AbGroup) : module_chain_complex rℤ -3ℤ.
let c . serre_spectral_sequence_map_of_is_conn (point _) f (EM_spectrum A) 0
  (is_strunc_EM_spectrum A) HB in
let cn : is_normal c . !is_normal_serre_spectral_sequence_map_of_is_conn in
have deg_d_x : forall (m : ℤ), deg (convergent_spectral_sequence.d c n) ((m - 1) - 1, n + 1) =
  (n + m - 0, 0),
Proof.
  intro m, refine deg_d_normal_eq cn _ _ @ _,
  refine prod_eq _ !add.right_inv,
  refine ap (fun x => x + (n+2)) !sub_sub @ _,
  refine add.comm4 m (- 2) n 2 @ _,
  refine ap (fun x => x + 0) !add.comm
Defined.,
have trivial_E : forall (r : ℕ) (p q : ℤ) (hq : q ≠ 0) (hq' : q ≠ of_nat (n+1)),
  is_contr (convergent_spectral_sequence.E c r (p, q)),
from gysin_trivial_Epage HB f e A,
have trivial_E' : forall (r : ℕ) (p q : ℤ) (hq : q > n+1),
  is_contr (convergent_spectral_sequence.E c r (p, q)),
from gysin_trivial_Epage2 HB f e A,
left_module.LES_of_SESs _ _ _ (fun m => convergent_spectral_sequence.d c n (m - 1, n + 1))
Proof.
  intro m,
  fapply short_exact_mod_isomorphism,
  rotate 3,
  { fapply short_exact_mod_of_is_contr_submodules
  (convergence_0 c (n + m) (fun m => neg_zero)),
  { exact zero_lt_succ n },
  { intro k Hk0 Hkn, apply trivial_E, exact fun h => Hk0 (of_nat.inj h),
  exact fun h => Hkn (of_nat.inj h), }},
  { symmetry, refine Einf_isomorphism c (n+1) _ _ @lm
  convergent_spectral_sequence.α c n (n + m - 0, 0) @lm
  isomorphism_of_eq (ap (graded_homology _ _) _) @lm
  !graded_homology_isomorphism @lm
  homology_isomorphism_cokernel_module _ _ _,
  { intros r Hr, apply trivial_E', apply of_nat_lt_of_nat_of_lt,
  rewrite [zero_add], exact lt_succ_of_le Hr },
  { intros r Hr, apply is_contr_E, apply is_normal.normal2 cn,
  refine lt_of_le_of_lt (le_of_eq (ap (fun x : ℤ \* ℤ => 0 + pr2 x) (is_normal.normal3 cn r))) _,
  esimp, rewrite [-sub_eq_add_neg], apply sub_lt_of_pos, apply of_nat_lt_of_nat_of_lt,
  apply succ_pos },
  { exact (deg_d_x m)^-1 },
  { intro x, apply @eq_of_is_contr, apply is_contr_E,
  apply is_normal.normal2 cn,
  refine lt_of_le_of_lt (@le_of_eq ℤ _ _ _ (ap (pr2 o deg (convergent_spectral_sequence.d c n))
  (deg_d_x m) @ ap pr2 (deg_d_normal_eq cn _ _))) _,
  refine lt_of_le_of_lt (le_of_eq (zero_add (-(n+1)))) _,
  apply neg_neg_of_pos, apply of_nat_succ_pos }},
  { reflexivity },
  { symmetry,
  refine Einf_isomorphism c (n+1) _ _ @lm
  convergent_spectral_sequence.α c n (n + m - (n+1), n+1) @lm
  graded_homology_isomorphism_kernel_module _ _ _ _ @lm
  isomorphism_of_eq (ap (graded_kernel _) _),
  { intros r Hr, apply trivial_E', apply of_nat_lt_of_nat_of_lt,
  apply lt_add_of_pos_right, apply zero_lt_succ },
  { intros r Hr, apply is_contr_E, apply is_normal.normal2 cn,
  refine lt_of_le_of_lt (le_of_eq (ap (fun x : ℤ \* ℤ => (n+1)+pr2 x) (is_normal.normal3 cn r))) _,
  esimp, rewrite [-sub_eq_add_neg], apply sub_lt_right_of_lt_add,
  apply of_nat_lt_of_nat_of_lt, rewrite [zero_add], exact lt_succ_of_le Hr },
  { apply trivial_image_of_is_contr, rewrite [deg_d_inv_eq],
  apply trivial_E', apply of_nat_lt_of_nat_of_lt,
  apply lt_add_of_pos_right, apply zero_lt_succ },
  { refine prod_eq _ rfl, refine ap (add _) !neg_add @ _,
  refine add.comm4 n m (-n) (- 1) @ _,
  refine ap (fun x => x + _) !add.right_inv @ !zero_add }}
Defined.

Definition gysin_sequence'_zero {E B : pType} {n : ℕ} (HB : is_conn 1 B) (f : E ->* B)
  (e : pfiber f <~>* sphere (n+1)) (A : AbGroup) (m : ℤ) :
  gysin_sequence' HB f e A (m, 0) <~>lm LeftModule_int_of_AbGroup (uoH^m+n+1[B, A]).
let c . serre_spectral_sequence_map_of_is_conn (point _) f (EM_spectrum A) 0
  (is_strunc_EM_spectrum A) HB in
let cn : is_normal c . !is_normal_serre_spectral_sequence_map_of_is_conn in
Proof.
  refine LES_of_SESs_zero _ _ m @lm _,
  transitivity convergent_spectral_sequence.E c n (m+n+1, 0),
  exact isomorphism_of_eq (ap (convergent_spectral_sequence.E c n)
  (deg_d_normal_eq cn _ _ @ prod_eq (add.comm4 m (- 1) n 2) (add.right_inv (n+1)))),
  refine E_isomorphism0 _ _ _ @lm
  lm_iso_int.mk (unreduced_ordinary_cohomology_isomorphism_right _ _ _),
  { intros r hr, apply is_contr_ordinary_cohomology,
  refine is_contr_equiv_closed_rev
  (equiv_of_isomorphism (cohomology_change_int _ _ _ @g uoH^<~>r+1[e^-1ᵉ*, A]))
  (unreduced_ordinary_cohomology_sphere_of_neq_nat A _ _),
  { exact !zero_sub @ ap neg (deg_d_normal_pr2 cn r) @ !neg_neg },
  { apply ne_of_lt, apply add_lt_add_right, exact hr },
  { apply succ_ne_zero }},
  { intros r hr, apply is_contr_ordinary_cohomology,
  refine is_contr_equiv_closed_rev
  (equiv_of_isomorphism (cohomology_change_int _ _ (!zero_add @ deg_d_normal_pr2 cn r)))
  (is_contr_ordinary_cohomology_of_neg _ _ _),
  { rewrite [-neg_zero], apply neg_lt_neg, apply of_nat_lt_of_nat_of_lt, apply zero_lt_succ }},
  { exact uoH^<~> 0[e^-1ᵉ*, A] @g unreduced_ordinary_cohomology_sphere_zero _ _ (succ_ne_zero n) }
Defined.

Definition gysin_sequence'_one {E B : pType} {n : ℕ} (HB : is_conn 1 B) (f : E ->* B)
  (e : pfiber f <~>* sphere (n+1)) (A : AbGroup) (m : ℤ) :
  gysin_sequence' HB f e A (m, 1) <~>lm LeftModule_int_of_AbGroup (uoH^m - 1[B, A]).
let c . serre_spectral_sequence_map_of_is_conn (point _) f (EM_spectrum A) 0
  (is_strunc_EM_spectrum A) HB in
let cn : is_normal c . !is_normal_serre_spectral_sequence_map_of_is_conn in
Proof.
  refine LES_of_SESs_one _ _ m @lm _,
  refine E_isomorphism0 _ _ _ @lm
  lm_iso_int.mk (unreduced_ordinary_cohomology_isomorphism_right _ _ _),
  { intros r hr, apply is_contr_ordinary_cohomology,
  refine is_contr_equiv_closed_rev
  (equiv_of_isomorphism uoH^<~>_[e^-1ᵉ*, A])
  (unreduced_ordinary_cohomology_sphere_of_gt _ _),
  { apply lt_add_of_pos_right, apply zero_lt_succ }},
  { intros r hr, apply is_contr_ordinary_cohomology,
  refine is_contr_equiv_closed_rev
  (equiv_of_isomorphism (cohomology_change_int _ _ _ @g uoH^<~>n-r[e^-1ᵉ*, A]))
  (unreduced_ordinary_cohomology_sphere_of_neq_nat A _ _),
  { refine ap (add _) (deg_d_normal_pr2 cn r) @ add_sub_comm n 1 r 1 @ !add_zero @ _,
  symmetry, apply of_nat_sub, exact le_of_lt hr },
  { apply ne_of_lt, exact lt_of_le_of_lt (nat.sub_le n r) (lt.base n) },
  { apply ne_of_gt, exact nat.sub_pos_of_lt hr }},
  { refine uoH^<~>n+1[e^-1ᵉ*, A] @g unreduced_ordinary_cohomology_sphere _ _ (succ_ne_zero n) }
Defined.

Definition gysin_sequence'_two {E B : pType} {n : ℕ} (HB : is_conn 1 B) (f : E ->* B)
  (e : pfiber f <~>* sphere (n+1)) (A : AbGroup) (m : ℤ) :
  gysin_sequence' HB f e A (m, 2) <~>lm LeftModule_int_of_AbGroup (uoH^n+m[E, A]).
LES_of_SESs_two _ _ m

Defined. cohomology
