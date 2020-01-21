(* pointed sequential colimits *)


import .seq_colim types.fin homotopy.chain_complex types.pointed2
open seq_colim pointed algebra eq is_trunc nat is_equiv equiv sigma sigma.ops chain_complex fiber

namespace seq_colim

Definition pseq_diagram (A : ℕ -> pType) : Type . forall n, A n ->* A (succ n)
Definition pseq_colim {X : ℕ -> pType} (f : pseq_diagram X) : pType.
  pointed.MK (seq_colim f) (@sι _ _ 0 (point _))

  variables {A A' : ℕ -> pType} {f : pseq_diagram A} {f' : pseq_diagram A'}
  {τ : forall n, A n ->* A' n} {H : forall n, τ (n+1) o* f n ==* f' n o* τ n}

Definition inclusion_pt {X : ℕ -> pType} (f : pseq_diagram X) (n : ℕ)
  : inclusion f (Point (X n)) = Point (pseq_colim f).
Proof.
  induction n with n p,
  reflexivity,
  exact (ap (sι f) (point_eq _))^-1ᵖ @ (!glue @ p)
Defined.

Definition pinclusion {X : ℕ -> pType} (f : pseq_diagram X) (n : ℕ)
  : X n ->* pseq_colim f.
  Build_pMap (inclusion f) (inclusion_pt f n)

Definition pshift_equiv {A : ℕ -> pType} (f : forall n, A n ->* A (succ n)) :
  pseq_colim f <~>* pseq_colim (fun n => f (n+1)).
Proof.
  fapply pequiv_of_equiv,
  { apply shift_equiv },
  { exact ap (ι _) (point_eq (f 0)) }
Defined.

Definition pshift_equiv_pinclusion {A : ℕ -> pType} (f : forall n, A n ->* A (succ n)) (n : ℕ) :
  psquare (pinclusion f n) (pinclusion (fun n => f (n+1)) n) (f n) (pshift_equiv f) .
  Build_pHomotopy homotopy.rfl begin
  refine (concat_1p _) @ _, esimp,
  induction n with n IH,
  { esimp[inclusion_pt], esimp[shift_diag], exact (concat_1p _)^-1 },
  { esimp[inclusion_pt], refine !con_inv_cancel_left @ _,
  rewrite ap_con, rewrite ap_con,
  refine _ @ whisker_right _ (concat_pp_p _ _ _),
  refine _ @ (con.assoc (_ @ _) _ _)^-1,
  xrewrite [-IH],
  esimp[shift_up], rewrite [elim_glue,  ap_inv, ap_compose'], esimp,
  rewrite [-+con.assoc], apply whisker_right,
  rewrite con.assoc, apply !eq_inv_con_of_con_eq,
  symmetry, exact eq_of_square !natural_square
  }
Defined.

Definition pseq_colim_functor {A A' : ℕ -> pType} {f : pseq_diagram A}
  {f' : pseq_diagram A'} (g : forall n, A n ->* A' n)
  (p : forall (n), g (n+1) o* f n == f' n o* g n) : pseq_colim f ->* pseq_colim f'.
  Build_pMap (seq_colim_functor g p) (ap (ι _) (point_eq (g _)))

Definition pseq_colim_pequiv' {A A' : ℕ -> pType} {f : pseq_diagram A}
  {f' : pseq_diagram A'} (g : forall n, A n <~>* A' n)
  (p : forall (n), g (n+1) o* f n == f' n o* g n) : pseq_colim @f <~>* pseq_colim @f'.
  pequiv_of_equiv (seq_colim_equiv g p) (ap (ι _) (point_eq (g _)))

Definition pseq_colim_pequiv {A A' : ℕ -> pType} {f : pseq_diagram A}
  {f' : pseq_diagram A'} (g : forall n, A n <~>* A' n)
  (p : forall n, g (n+1) o* f n ==* f' n o* g n) : pseq_colim @f <~>* pseq_colim @f'.
  pseq_colim_pequiv' g (fun n => @p n)


Definition pseq_colim_equiv_constant' {A : ℕ -> pType} {f f' : pseq_diagram A}
  (p : forall (n), f n == f' n) : pseq_colim @f <~>* pseq_colim @f'.
  pseq_colim_pequiv' (fun n => pequiv.rfl) p

Definition pseq_colim_equiv_constant {A : ℕ -> pType} {f f' : pseq_diagram A}
  (p : forall n, f n ==* f' n) : pseq_colim @f <~>* pseq_colim @f'.
  pseq_colim_pequiv (fun n => pequiv.rfl) (fun n => !pid_pcompose @* p n @* !pcompose_pid^-1*)

Definition pseq_colim_pequiv_pinclusion {A A' : ℕ -> pType} {f : forall n, A n ->* A (n+1)}
  {f' : forall n, A' n ->* A' (n+1)} (g : forall n, A n <~>* A' n)
  (p : forall (n), g (n+1) o* f n ==* f' n o* g n) (n : ℕ) :
  psquare (pinclusion f n) (pinclusion f' n) (g n) (pseq_colim_pequiv g p).
  Build_pHomotopy homotopy.rfl begin
  esimp, refine (concat_1p _) @ _,
  induction n with n IH,
  { esimp[inclusion_pt], exact (concat_1p _)^-1 },
  { esimp[inclusion_pt], rewrite [+ap_con, -+ap_inv, +con.assoc, +seq_colim_functor_glue] =>
  xrewrite[-IH],
  rewrite[+ap_compose', -+con.assoc],
  apply whisker_right, esimp,
  rewrite[(eq_con_inv_of_con_eq (point_htpy (@p _)))],
  rewrite[ap_con], esimp,
  rewrite[-+con.assoc, ap_con, ap_compose', +ap_inv],
  rewrite[-+con.assoc],
  refine _ @ whisker_right _ (whisker_right _ (whisker_right _ (whisker_right _ (con_Vp _)^-1))),
  rewrite[idp_con, +con.assoc], apply whisker_left,
  rewrite[ap_con, ap_compose', con_inv, +con.assoc], apply whisker_left,
  refine eq_inv_con_of_con_eq _,
  symmetry, exact eq_of_square !natural_square
  }
Defined.

Definition seq_colim_equiv_constant_pinclusion {A : ℕ -> pType} {f f' : pseq_diagram A}
  (p : forall n, f n ==* f' n) (n : ℕ) :
  pseq_colim_equiv_constant p o* pinclusion f n ==* pinclusion f' n .
Proof.
  transitivity pinclusion f' n o* !pid,
  refine phomotopy_of_psquare !pseq_colim_pequiv_pinclusion,
  exact !pcompose_pid
Defined.

Definition pseq_colim.elim' {A : ℕ -> pType} {B : pType} {f : pseq_diagram A}
  (g : forall n, A n ->* B) (p : forall n, g (n+1) o* f n == g n) : pseq_colim f ->* B.
Proof.
  fapply Build_pMap,
  { intro x, induction x with n a n a,
  { exact g n a },
  { exact p n a }},
  { esimp, apply point_eq }
Defined.

Definition pseq_colim.elim {A : ℕ -> pType} {B : pType} {f : pseq_diagram A}
  (g : forall n, A n ->* B) (p : forall n, g (n+1) o* f n ==* g n) : pseq_colim @f ->* B.
  pseq_colim.elim' g p

Definition pseq_colim.elim_pinclusion {A : ℕ -> pType} {B : pType} {f : pseq_diagram A}
  (g : forall n, A n ->* B) (p : forall n, g (n+1) o* f n ==* g n) (n : ℕ) :
  pseq_colim.elim g p o* pinclusion f n ==* g n.
Proof.
  refine Build_pHomotopy (reflexivity _) _,
  refine (concat_1p _) @ _,
  esimp,
  induction n with n IH,
  { esimp, esimp[inclusion_pt], exact (concat_1p _)^-1 },
  { esimp, esimp[inclusion_pt],
  rewrite ap_con, rewrite ap_con,
  rewrite elim_glue,
  rewrite [-ap_inv],
  rewrite [ap_compose'], esimp,
  rewrite [(eq_con_inv_of_con_eq (!point_htpy))],
  rewrite [IH],
  rewrite [con_inv],
  rewrite [-+con.assoc],
  refine _ @ whisker_right _ (concat_pp_p _ _ _)^-1,
  rewrite [con.left_inv], esimp,
  refine _ @ (concat_pp_p _ _ _)^-1,
  rewrite [con.left_inv], esimp,
  rewrite [ap_inv],
  rewrite [-con.assoc],
  refine (concat_1p _)^-1 @ whisker_right _ (con_Vp _)^-1,
  }
Defined.

Definition prep0 {A : ℕ -> pType} (f : pseq_diagram A) (k : ℕ) : A 0 ->* A k.
  Build_pMap (rep0 (fun n x => f n x) k)
Proof. induction k with k p, reflexivity, exact ap (@f k) p @ !point_eq end

Definition point_eq_prep0_succ {A : ℕ -> pType} (f : pseq_diagram A) (k : ℕ)
  : point_eq (prep0 f (succ k)) = ap (@f k) (point_eq (prep0 f k)) @ point_eq (f k).
  by reflexivity

Definition prep0_succ_lemma {A : ℕ -> pType} (f : pseq_diagram A) (n : ℕ)
  (p : rep0 (fun n x => f n x) n (point _) = rep0 (fun n x => f n x) n (point _))
  (q : prep0 f n (Point (A 0)) = Point (A n))
  : loop_equiv_eq_closed (ap (@f n) q @ point_eq (@f n))
  (ap (@f n) p) = Ω->(@f n) (loop_equiv_eq_closed q p).
  by rewrite [▸*, con_inv, ↑ap1_gen, +ap_con, ap_inv, +con.assoc]





Definition pseq_colim_loop {X : ℕ -> pType} (f : forall n, X n ->* X (n+1)) :
  loops (pseq_colim f) <~>* pseq_colim (fun n => Ω-> (f n)).
Proof.
  fapply pequiv_of_equiv,
  { refine !seq_colim_eq_equiv0 @e _,
  fapply seq_colim_equiv,
  { intro n, exact loop_equiv_eq_closed (point_eq (prep0 f n)) },
  { intro n p, apply prep0_succ_lemma }},
  { reflexivity }
Defined.

Definition pseq_colim_loop_pinclusion {X : ℕ -> pType} (f : forall n, X n ->* X (n+1)) (n : ℕ) :
  pseq_colim_loop f o* Ω-> (pinclusion f n) ==* pinclusion (fun n => Ω->(f n)) n.
  sorry

Definition pseq_colim_loop_natural (n : ℕ) : psquare (pseq_colim_loop f) (pseq_colim_loop f')
  (Ω-> (pseq_colim_functor τ H)) (pseq_colim_functor (fun n => Ω-> (τ n)) (fun n => ap1_psquare (H n))).
  sorry

Definition pseq_diagram_pfiber {A A' : ℕ -> pType} {f : pseq_diagram A} {f' : pseq_diagram A'}
  (g : forall n, A n ->* A' n) (p : forall n, g (succ n) o* f n ==* f' n o* g n) :
  pseq_diagram (fun k => pfiber (g k)).
  fun k => pfiber_functor (f k) (f' k) (p k)

(* Two issues when going to the pointed version of the fiber commuting with colimit:
  - seq_diagram_fiber τ p a for a : A n at position k lives over (A (n + k)), so for a : A 0 you get A (0 + k), but we need A k
  - in seq_diagram_fiber the fibers are taken in rep f ..., but in the pointed version over the basepoint of A n
*)
Definition pfiber_pseq_colim_functor {A A' : ℕ -> pType} {f : pseq_diagram A}
  {f' : pseq_diagram A'} (τ : forall n, A n ->* A' n)
  (p : forall (n), τ (n+1) o* f n ==* f' n o* τ n) : pfiber (pseq_colim_functor τ p) <~>*
  pseq_colim (pseq_diagram_pfiber τ p).
Proof.
  fapply pequiv_of_equiv,
  { refine fiber_seq_colim_functor0 τ p (point _) @e _ => fapply seq_colim_equiv, intro n, esimp,
  repeat exact sorry }, exact sorry
Defined.





print axioms pseq_colim_loop

Defined. seq_colim
