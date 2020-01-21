(* Spectral sequences
  - basic properties of spectral sequences
  - currently, we only construct an spectral sequence from an exact couple
 *)


import .exact_couple

open algebra is_trunc left_module is_equiv equiv eq function nat sigma set_quotient group
  left_module group int prod prod.ops
open exact_couple (Z2)

structure convergent_spectral_sequence.{u v w} {R : Ring} (E' : ℤ -> ℤ -> LeftModule.{u v} R)
  (Dinf : ℤ -> LeftModule.{u w} R) : Type.{max u (v+1) (w+1)}.
  (E : ℕ -> graded_module.{u 0 v} R Z2)
  (d : forall (r : ℕ), E r ->gm E r)
  (deg_d : ℕ -> Z2)
  (deg_d_eq0 : forall (r : ℕ), deg (d r) 0 = deg_d r)
  (α : forall (r : ℕ) (x : Z2), E (r+1) x <~>lm graded_homology (d r) (d r) x)
  (e : forall (x : Z2), E 0 x <~>lm E' x.1 x.2)
  (s₀ : Z2 -> ℕ)
  (f : forall {r : ℕ} {x : Z2} (h : s₀ x ≤ r), E (s₀ x) x <~>lm E r x)
  (lb : ℤ -> ℤ)
  (HDinf : forall (n : ℤ), is_built_from (Dinf n)
  (fun (k : ℕ) => (fun x => E (s₀ x) x) (n - (k + lb n), k + lb n)))
(* todo: the currentDefinition doesn't say that E (s₀ x) x is contractible for x.1 + x.2 = n and x.2 < lb n *)

Definition convergent_spectral_sequence_g (E' : ℤ -> ℤ -> AbGroup)
  (Dinf : ℤ -> AbGroup) : Type.
convergent_spectral_sequence (fun n s => LeftModule_int_of_AbGroup (E' n s))
  (fun n => LeftModule_int_of_AbGroup (Dinf n))

  section exact_couple
  open exact_couple exact_couple.exact_couple exact_couple.convergent_exact_couple
  exact_couple.convergence_Definition exact_couple.derived_couple

Definition convergent_spectral_sequence_of_exact_couple {R : Ring} {E' : ℤ -> ℤ -> LeftModule R}
  {Dinf : ℤ -> LeftModule R} (c : convergent_exact_couple E' Dinf)
  (st_eq : forall n, (st c n).1 + (st c n).2 = n) (deg_i_eq : deg (i (X c)) 0 = (- 1, 1)) :
  convergent_spectral_sequence E' Dinf.
  convergent_spectral_sequence.mk (fun r => E (page (X c) r)) (fun r => d (page (X c) r))
  (deg_d c) (deg_d_eq0 c)
  (fun r ns => by reflexivity) (e c) (B3 (HH c)) (fun r ns Hr => Einfstable (HH c) Hr idp)
  (fun n => (st c n).2)
Proof.
  intro n,
  refine is_built_from_isomorphism (f c n) _ (is_built_from_infpage (HH c) (st c n) (HB c n)),
  intro p, apply isomorphism_of_eq, apply ap (fun x => E (page (X c) (B3 (HH c) x)) x),
  induction p with p IH,
  { exact !prod.eta^-1 @ prod_eq (eq_sub_of_add_eq (ap (add _) !zero_add @ st_eq n))
  (zero_add (st c n).2)^-1 },
  { assert H1 : forall (a : ℤ), n - (p + a) - 1 = n - (succ p + a),
  exact fun a => !sub_add_eq_sub_sub^-1 @ ap (sub n) (add_comm_middle p a 1 @ proof idp qed),
  assert H2 : forall (a : ℤ), p + a + 1 = succ p + a,
  exact fun a => add_comm_middle p a 1,
  refine ap (deg (i (X c))) IH @ !deg_eq @ ap (add _) deg_i_eq @ prod_eq !H1 !H2 }
Defined.
Defined. exact_couple

namespace spectral_sequence
  open convergent_spectral_sequence

  variables {R : Ring} {E' : ℤ -> ℤ -> LeftModule R} {Dinf : ℤ -> LeftModule R}
  (c : convergent_spectral_sequence E' Dinf)


Definition Einf (x : Z2) : LeftModule R . E c (s₀ c x) x

Definition is_contr_E_succ (r : ℕ) (x : Z2) (h : is_contr (E c r x)) : is_contr (E c (r+1) x).
  is_contr_equiv_closed_rev (equiv_of_isomorphism (α c r x)) (is_contr_homology _ _ _)

Definition deg_d_eq (r : ℕ) (x : Z2) : deg (d c r) x = x + deg_d c r.
  !deg_eq @ ap (add _) !deg_d_eq0

Definition deg_d_inv_eq (r : ℕ) (x : Z2) : (deg (d c r))^-1ᵉ x = x - deg_d c r.
  inv_eq_of_eq (!deg_d_eq @ !neg_add_cancel_right)^-1

Definition is_contr_E_of_le {r₁ r₂ : ℕ} (H : r₁ ≤ r₂) (x : Z2) (h : is_contr (E c r₁ x)) :
  is_contr (E c r₂ x).
Proof.
  induction H with r₂ H IH,
  { exact h },
  { apply is_contr_E_succ, exact IH }
Defined.

Definition is_contr_E (r : ℕ) (x : Z2) (h : is_contr (E' x.1 x.2)) : is_contr (E c r x).
  is_contr_E_of_le c !zero_le x (is_contr_equiv_closed_rev (equiv_of_isomorphism (e c x)) h)

Definition is_contr_Einf (x : Z2) (h : is_contr (E' x.1 x.2)) : is_contr (Einf c x).
  is_contr_E c (s₀ c x) x h

Definition E_isomorphism {r₁ r₂ : ℕ} {ns : Z2} (H : r₁ ≤ r₂)
  (H1 : forall (r), r₁ ≤ r -> r < r₂ -> is_contr (E c r (ns - deg_d c r)))
  (H2 : forall (r), r₁ ≤ r -> r < r₂ -> is_contr (E c r (ns + deg_d c r))) :
  E c r₂ ns <~>lm E c r₁ ns.
Proof.
  assert H3 : forall (r), r₁ ≤ r -> r ≤ r₂ -> E c r ns <~>lm E c r₁ ns,
  { intro r Hr₁ Hr₂,
  induction Hr₁ with r Hr₁ IH, reflexivity,
  let Hr₂' . le_of_succ_le Hr₂,
  refine α c r ns  @lm homology_isomorphism _ _ _ _ @lm IH Hr₂',
  exact is_contr_equiv_closed (equiv_ap (E c r) !deg_d_inv_eq^-1) (H1 Hr₁ Hr₂),
  exact is_contr_equiv_closed (equiv_ap (E c r) !deg_d_eq^-1) (H2 Hr₁ Hr₂) },
  exact H3 H (le.refl _)
Defined.

Definition E_isomorphism0 {r : ℕ} {n s : ℤ}
  (H1 : forall r', r' < r -> is_contr (E' (n - (deg_d c r').1) (s - (deg_d c r').2)))
  (H2 : forall r', r' < r -> is_contr (E' (n + (deg_d c r').1) (s + (deg_d c r').2))) :
  E c r (n, s) <~>lm E' n s.
  E_isomorphism c !zero_le (fun r' Hr₁ Hr₂ => is_contr_E c r' _ (H1 r' Hr₂))
  (fun r' Hr₁ Hr₂ => is_contr_E c r' _ (H2 r' Hr₂)) @lm
  e c (n, s)

Definition Einf_isomorphism (r₁ : ℕ) {ns : Z2}
  (H1 : forall (r), r₁ ≤ r -> is_contr (E c r (ns - deg_d c r)))
  (H2 : forall (r), r₁ ≤ r -> is_contr (E c r (ns + deg_d c r))) :
  Einf c ns <~>lm E c r₁ ns.
Proof.
  cases le.total r₁ (s₀ c ns) with Hr Hr,
  exact E_isomorphism c Hr (fun r Hr₁ Hr₂ => H1 Hr₁) (fun r Hr₁ Hr₂ => H2 Hr₁),
  exact f c Hr
Defined.

Definition Einf_isomorphism0 {n s : ℤ}
  (H1 : forall r, is_contr (E' (n - (deg_d c r).1) (s - (deg_d c r).2)))
  (H2 : forall r, is_contr (E' (n + (deg_d c r).1) (s + (deg_d c r).2))) :
  Einf c (n, s) <~>lm E' n s.
  E_isomorphism0 c (fun r Hr => H1 r) (fun r Hr => H2 r)

Definition convergence_0 (n : ℤ) (H : forall m, lb c m = 0) :
  is_built_from (Dinf n) (fun (k : ℕ) => Einf c (n - k, k)).
  is_built_from_isomorphism isomorphism.rfl
  (fun k => left_module.isomorphism_of_eq (ap (Einf c)
  (prod_eq (ap (sub n) (ap (add _) !H @ add_zero _)) (ap (add _) !H @ add_zero _))))
  (HDinf c n)

  (* we call a spectral sequence normal if it is a first-quadrant spectral sequence and
  the degree of d on page r (for r ≥ 2) is (r, -(r-1)).
  The indexing is different, because we start counting pages at 2. *)
  include c
  structure is_normal : Type.
  (normal1 : forall {n} s, n < 0 -> is_contr (E' n s))
  (normal2 : forall n {s}, s < 0 -> is_contr (E' n s))
  (normal3 : forall (r : ℕ), deg_d c r = (r+2, -(r+1)))
  open is_normal
  variable {c}
  variable (nc : is_normal c)
  include nc

Definition deg_d_normal_pr1 (r : ℕ) : (deg_d c r).1 = r+2    . ap pr1 (normal3 nc r)
Definition deg_d_normal_pr2 (r : ℕ) : (deg_d c r).2 = -(r+1) . ap pr2 (normal3 nc r)

Definition stable_range {n s : ℤ} {r : ℕ} (H1 : n < r + 2) (H2 : s < r + 1) :
  Einf c (n, s) <~>lm E c r (n, s).
Proof.
  fapply Einf_isomorphism,
  { intro r' Hr', apply is_contr_E, apply normal1 nc,
  refine lt_of_le_of_lt (le_of_eq (ap (fun x => n - x.1) (normal3 nc r'))) _,
  apply sub_lt_left_of_lt_add,
  refine lt_of_lt_of_le H1 (le.trans _ (le_of_eq !add_zero^-1)),
  exact add_le_add_right (of_nat_le_of_nat_of_le Hr') 2 },
  { intro r' Hr', apply is_contr_E, apply normal2 nc,
  refine lt_of_le_of_lt (le_of_eq (ap (fun x => s + x.2) (normal3 nc r'))) _,
  change s - (r' + 1) < 0,
  apply sub_lt_left_of_lt_add,
  refine lt_of_lt_of_le H2 (le.trans _ (le_of_eq !add_zero^-1)),
  exact add_le_add_right (of_nat_le_of_nat_of_le Hr') 1 },
Defined.

Definition deg_d_normal_eq (r : ℕ) (x : Z2) : deg (d c r) x = x + (r+2, -(r+1)).
  deg_d_eq c r x @ ap (add x) (is_normal.normal3 nc r)

  omit nc


Defined. spectral_sequence
