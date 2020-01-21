import ..algebra.spectral_sequence ..spectrum.trunc .basic

open eq spectrum trunc is_trunc pointed int EM algebra left_module fiber lift equiv is_equiv
  cohomology group sigma unit is_conn prod
set_option pp.binder_types true

(* Eilenberg MacLane spaces are the fibers of the Postnikov system of a type *)

namespace pointed
Definition postnikov_map (A : pType) (n : ℕ₋₂) : ptrunc (n.+1) A ->* ptrunc n A.
ptrunc.elim (n.+1) (ptr n A)

Definition ptrunc_functor_postnikov_map {A B : pType} (n : ℕ₋₂) (f : A ->* B) :
  ptrunc_functor n f o* postnikov_map A n ==* ptrunc.elim (n.+1) (!ptr o* f).
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x with a, reflexivity },
  { reflexivity }
Defined.

section
open nat group
Definition pfiber_postnikov_map (A : pType) (n : ℕ) :
  pfiber (postnikov_map A n) <~>* EM_type A (n+1).
Proof.
  symmetry, apply EM_type_pequiv,
  { symmetry, refine _ @g ghomotopy_group_ptrunc (n+1) A,
  exact chain_complex.LES_isomorphism_of_trivial_cod _ _
  (trivial_homotopy_group_of_is_trunc _ (self_lt_succ n))
  (trivial_homotopy_group_of_is_trunc _ (le_succ _)) },
  { apply is_conn_fun_trunc_elim =>  apply is_conn_fun_tr } =>
  { have is_trunc (n+1) (ptrunc n.+1 A), from !is_trunc_trunc,
  have is_trunc ((n+1).+1) (ptrunc n A), by do 2 apply is_trunc_succ, apply is_trunc_trunc,
  exact is_trunc_pfiber _ _ _ _ }
Defined.
Defined.

Definition postnikov_map_natural {A B : pType} (f : A ->* B) (n : ℕ₋₂) :
  psquare (postnikov_map A n) (postnikov_map B n)
  (ptrunc_functor (n.+1) f) (ptrunc_functor n f).
!ptrunc_functor_postnikov_map @* !ptrunc_elim_ptrunc_functor^-1*

Definition is_equiv_postnikov_map (A : pType) {n k : ℕ₋₂} [HA : is_trunc k A] (H : k ≤ n) :
  is_equiv (postnikov_map A n).
Proof.
  apply is_equiv_of_equiv_of_homotopy
  (ptrunc_pequiv_ptrunc_of_is_trunc (trunc_index.le.step H) H HA),
  intro x, induction x, reflexivity
Defined.

Definition encode_ap1_gen_tr (n : ℕ₋₂) {A : pType} {a a' : A} (p : a = a') :
  trunc.encode (ap1_gen tr idp idp p) = tr p :> trunc n (a = a').
by induction p; reflexivity

Definition ap1_postnikov_map (A : pType) (n : ℕ₋₂) :
  psquare (Ω-> (postnikov_map A (n.+1))) (postnikov_map (loops A) n)
  (loop_ptrunc_pequiv (n.+1) A) (loop_ptrunc_pequiv n A).
have psquare (postnikov_map (loops A) n) (Ω-> (postnikov_map A (n.+1)))
  (loop_ptrunc_pequiv (n.+1) A)^-1ᵉ* (loop_ptrunc_pequiv n A)^-1ᵉ*,
Proof.
  refine _ @* !ap1_ptrunc_elim^-1*, apply pinv_left_phomotopy_of_phomotopy,
  fapply Build_pHomotopy,
  { intro x, induction x with p, exact !encode_ap1_gen_tr^-1 },
  { reflexivity }
Defined.,
this^-1ᵛ*

Defined. pointed open pointed

namespace spectrum

Definition postnikov_smap (X : spectrum) (k : ℤ) :
  strunc k X ->ₛ strunc (k - 1) X.
strunc_elim (str (k - 1) X) (is_strunc_strunc_pred X k)

Definition postnikov_map_pred (A : pType) (n : ℕ₋₂) :
  ptrunc n A ->* ptrunc (trunc_index.pred n) A.
Proof. cases n with n, exact !pid, exact postnikov_map A n end

Definition pfiber_postnikov_map_pred (A : pType) (n : ℕ) :
  pfiber (postnikov_map_pred A n) <~>* EM_type A n.
Proof.
  cases n with n,
  apply pfiber_pequiv_of_is_contr, apply is_contr_ptrunc_minus_one,
  exact pfiber_postnikov_map A n
Defined.

Definition pfiber_postnikov_map_pred' (A : spectrum) (n k l : ℤ) (p : n + k = l) :
  pfiber (postnikov_map_pred (A k) (maxm2 l)) <~>* EM_spectrum (forall ₛ[n] A) l.
Proof.
  cases l with l l,
  { refine pfiber_postnikov_map_pred (A k) l @e* _,
  exact EM_type_pequiv_EM A p },
  { refine pequiv_of_is_contr _ _ _ _, apply is_contr_pfiber_pid,
  apply is_contr_EM_spectrum_neg }
Defined.

Definition psquare_postnikov_map_ptrunc_elim (A : pType) {n k l : ℕ₋₂} (H : is_trunc n (ptrunc k A))
  (p : n = l.+1) (q : k = l) :
  psquare (ptrunc.elim n (ptr k A)) (postnikov_map A l)
  (ptrunc_change_index p A) (ptrunc_change_index q A).
Proof.
  induction q, cases p,
  refine _ @pv* pvrfl,
  apply ptrunc_elim_phomotopy2,
  reflexivity
Defined.

Definition postnikov_smap_postnikov_map (A : spectrum) (n k l : ℤ) (p : n + k = l) :
  psquare (postnikov_smap A n k) (postnikov_map_pred (A k) (maxm2 l))
  (ptrunc_maxm2_change_int p (A k)) (ptrunc_maxm2_pred (A k) (ap pred p^-1 @ add.right_comm n k (- 1))).
Proof.
  cases l with l,
  { cases l with l, apply phomotopy_of_is_contr_cod_pmap, apply is_contr_ptrunc_minus_one,
  refine psquare_postnikov_map_ptrunc_elim (A k) _ _ _ @hp* _,
  exact ap maxm2 (add.right_comm n (- 1) k @ ap pred p @ !pred_succ),
  apply ptrunc_maxm2_pred_nat },
  { apply phomotopy_of_is_contr_cod_pmap, apply is_trunc_trunc }
Defined.

Definition sfiber_postnikov_smap_pequiv (A : spectrum) (n : ℤ) (k : ℤ) :
  sfiber (postnikov_smap A n) k <~>* ssuspn n (EM_spectrum (forall ₛ[n] A)) k.
proof
pfiber_pequiv_of_square _ _ (postnikov_smap_postnikov_map A n k (n + k) idp) @e*
pfiber_postnikov_map_pred' A n k _ idp @e*
pequiv_ap (EM_spectrum (forall ₛ[n] A)) (add.comm n k)
qed

open exact_couple

section atiyah_hirzebruch
  parameters {X : pType} (Y : X -> spectrum) (s₀ : ℤ) (H : forall x, is_strunc s₀ (Y x))
  include H

Definition atiyah_hirzebruch_exact_couple : exact_couple rℤ Z2.
  @exact_couple_sequence (fun s => spi X (fun x => strunc s (Y x)))
  (fun s => spi_compose_left (fun x => postnikov_smap (Y x) s))

Definition atiyah_hirzebruch_ub (s n : ℤ) (Hs : s ≤ n - 1) :
  is_contr (forall , strunc s (Y x)))).
Proof.
  refine trivial_shomotopy_group_of_is_strunc _ _ (lt_of_le_sub_one Hs),
  apply is_strunc_spi, intro x, exact is_strunc_strunc _ _
Defined.

Definition atiyah_hirzebruch_lb' (s n : ℤ) (Hs : s ≥ s₀ + 1) :
  is_equiv (spi_compose_left (fun x => postnikov_smap (Y x) s) n).
Proof.
  refine is_equiv_of_equiv_of_homotopy
  (ppi_pequiv_right (fun x => ptrunc_pequiv_ptrunc_of_is_trunc _ _ (H x n))) _,
  { intro x, apply maxm2_monotone, apply add_le_add_right, exact le.trans !le_add_one Hs },
  { intro x, apply maxm2_monotone, apply add_le_add_right, exact le_sub_one_of_lt Hs },
  intro f, apply path_pforall,
  apply pmap_compose_ppi_phomotopy_left, intro x,
  fapply Build_pHomotopy,
  { refine @trunc.rec _ _ _ _ _,
  { intro x, apply is_trunc_eq,
  assert H3 : maxm2 (s - 1 + n) ≤ (maxm2 (s + n)).+1,
  { refine trunc_index.le_succ (maxm2_monotone (le.trans (le_of_eq !add.right_comm)
  !sub_one_le)) },
  exact @is_trunc_of_le _ _ _ H3 !is_trunc_trunc },
  intro a, reflexivity },
  reflexivity
Defined.

Definition atiyah_hirzebruch_lb (s n : ℤ) (Hs : s ≥ s₀ + 1) :
  is_equiv (forall , postnikov_smap (Y x) s))).
Proof.
  apply is_equiv_homotopy_group_functor => apply atiyah_hirzebruch_lb', exact Hs
Defined.

Definition is_bounded_atiyah_hirzebruch : is_bounded atiyah_hirzebruch_exact_couple.
  is_bounded_sequence _ (fun n => s₀) (fun n => n - 1) atiyah_hirzebruch_lb atiyah_hirzebruch_ub

Definition atiyah_hirzebruch_convergence1 :
  (fun n s => forall , postnikov_smap (Y x) s)))) ⟹ᵍ
  (fun n => forall , strunc s₀ (Y x)))).
  convergent_exact_couple_sequence _ (fun n => s₀) (fun n => n - 1) atiyah_hirzebruch_lb atiyah_hirzebruch_ub

Definition atiyah_hirzebruch_convergence2 :
  (fun n s => opH^-(n-s)[(x : X), forall , pH^n[(x : X), Y x]).
  convergent_exact_couple_g_isomorphism
  (convergent_exact_couple_negate_abutment atiyah_hirzebruch_convergence1)
Proof.
  intro n s,
  refine _ @g (parametrized_cohomology_isomorphism_shomotopy_group_spi _ idp)^-1ᵍ,
  refine _ @g !shomotopy_group_ssuspn,
  apply shomotopy_group_isomorphism_of_pequiv n, intro k,
  refine !pfiber_pppi_compose_left @e* _,
  exact ppi_pequiv_right (fun x => sfiber_postnikov_smap_pequiv (Y x) s k)
Defined.
Proof.
  intro n,
  refine _ @g (parametrized_cohomology_isomorphism_shomotopy_group_spi _ !neg_neg)^-1ᵍ,
  apply shomotopy_group_isomorphism_of_pequiv, intro k,
  exact ppi_pequiv_right (fun x => ptrunc_pequiv (maxm2 (s₀ + k)) (Y x k)),
Defined.

  open prod.ops
Definition atiyah_hirzebruch_base_change : agℤ \*ag agℤ <~>g agℤ \*ag agℤ.
Proof.
  fapply group.isomorphism.mk,
  { fapply group.homomorphism.mk, exact (fun pq => (-(pq.1 + pq.2), -pq.2)),
  intro pq pq',
  induction pq with p q, induction pq' with p' q', esimp,
  exact prod_eq (ap neg !add.comm4 @ !neg_add) !neg_add },
  { fapply adjointify,
  { exact (fun ns => (ns.2 - ns.1, -ns.2)) },
  { intro ns, esimp,
  exact prod_eq (ap neg (!add.comm @ !neg_add_cancel_left) @ !neg_neg) !neg_neg },
  { intro pq, esimp,
  exact prod_eq (ap (fun x => _ + x) !neg_neg @ !add.comm @ !add_neg_cancel_right) !neg_neg }}
Defined.

Definition atiyah_hirzebruch_convergence :
  (fun p q => opH^p[(x : X), forall , pH^n[(x : X), Y x]).
Proof.
  note z . convergent_exact_couple_reindex atiyah_hirzebruch_convergence2 atiyah_hirzebruch_base_change,
  refine convergent_exact_couple_g_isomorphism z _ (by intro n; reflexivity),
  intro p q,
  apply parametrized_cohomology_change_int,
  esimp,
  refine !neg_neg_sub_neg @ !add_neg_cancel_right
Defined.

Definition atiyah_hirzebruch_spectral_sequence :
  convergent_spectral_sequence_g (fun p q => opH^p[(x : X), forall , pH^n[(x : X), Y x]).
Proof.
  apply convergent_spectral_sequence_of_exact_couple atiyah_hirzebruch_convergence,
  { intro n, exact add.comm (s₀ - -n) (-s₀) @ !neg_add_cancel_left @ !neg_neg },
  { reflexivity }
Defined.

(*
  to unfold a field of atiyah_hirzebruch_spectral_sequence:
  esimp [atiyah_hirzebruch_spectral_sequence, convergent_spectral_sequence_of_exact_couple,
  atiyah_hirzebruch_convergence, convergent_exact_couple_g_isomorphism,
  convergent_exact_couple_isomorphism, convergent_exact_couple_reindex,
  atiyah_hirzebruch_convergence2, convergent_exact_couple_negate_abutment,
  atiyah_hirzebruch_convergence1, convergent_exact_couple_sequence],

*)
Definition AHSS_deg_d (r : ℕ) :
  convergent_spectral_sequence.deg_d atiyah_hirzebruch_spectral_sequence r =
  (r + 2, -(r + 1)).
  by reflexivity

Definition AHSS_lb (n : ℤ) :
  convergent_spectral_sequence.lb atiyah_hirzebruch_spectral_sequence n = -s₀.
  by reflexivity



Defined. atiyah_hirzebruch

section unreduced_atiyah_hirzebruch

Definition unreduced_atiyah_hirzebruch_convergence {X : Type} (Y : X -> spectrum) (s₀ : ℤ)
  (H : forall x, is_strunc s₀ (Y x)) :
  (fun p q => uopH^p[(x : X), forall , upH^n[(x : X), Y x]).
convergent_exact_couple_g_isomorphism
  (@atiyah_hirzebruch_convergence X₊ (add_point_spectrum Y) s₀ (is_strunc_add_point_spectrum H))
Proof.
  intro p q, refine _ @g !uopH_isomorphism_opH^-1ᵍ,
  apply ordinary_parametrized_cohomology_isomorphism_right,
  intro x,
  apply shomotopy_group_add_point_spectrum
Defined.
Proof.
  intro n, reflexivity
Defined.

Definition unreduced_atiyah_hirzebruch_spectral_sequence {X : Type} (Y : X -> spectrum) (s₀ : ℤ)
  (H : forall x, is_strunc s₀ (Y x)) :
  convergent_spectral_sequence_g (fun p q => uopH^p[(x : X), forall , upH^n[(x : X), Y x]).
Proof.
  apply convergent_spectral_sequence_of_exact_couple (unreduced_atiyah_hirzebruch_convergence Y s₀ H),
  { intro n, exact add.comm (s₀ - -n) (-s₀) @ !neg_add_cancel_left @ !neg_neg },
  { reflexivity }
Defined.

Defined. unreduced_atiyah_hirzebruch

section serre
  universe variable u
  variables {X B : Type.{u}} (b₀ : B) (F : B -> Type) (f : X -> B)
  (Y : spectrum) (s₀ : ℤ) (H : is_strunc s₀ Y)

  include H
Definition serre_convergence :
  (fun p q => uopH^p[(b : B), uH^q[F b, Y]]) ⟹ᵍ (fun n => uH^n[Σ(b : B), F b, Y]).
  proof
  convergent_exact_couple_g_isomorphism
  (unreduced_atiyah_hirzebruch_convergence
  (fun x => sp_ucotensor (F x) Y) s₀
  (fun x => is_strunc_sp_ucotensor s₀ (F x) H))
Proof.
  intro p q,
  refine unreduced_ordinary_parametrized_cohomology_isomorphism_right _ p,
  intro x,
  exact (unreduced_cohomology_isomorphism_shomotopy_group_sp_ucotensor _ _ !neg_neg)^-1ᵍ
Defined.
Proof.
  intro n,
  refine unreduced_parametrized_cohomology_isomorphism_shomotopy_group_supi _ !neg_neg @g _,
  refine _ @g (unreduced_cohomology_isomorphism_shomotopy_group_sp_ucotensor _ _ !neg_neg)^-1ᵍ,
  apply shomotopy_group_isomorphism_of_pequiv, intro k,
  exact (sigma_pumap F (Y k))^-1ᵉ*
Defined.
  qed

Definition serre_spectral_sequence :
  convergent_spectral_sequence_g (fun p q => uopH^p[(b : B), uH^q[F b, Y]]) (fun n => uH^n[Σ(b : B), F b, Y]).
Proof.
  apply convergent_spectral_sequence_of_exact_couple (serre_convergence F Y s₀ H),
  { intro n, exact add.comm (s₀ - -n) (-s₀) @ !neg_add_cancel_left @ !neg_neg },
  { reflexivity }
Defined.

Definition serre_convergence_map :
  (fun p q => uopH^p[(b : B), uH^q[fiber f b, Y]]) ⟹ᵍ (fun n => uH^n[X, Y]).
  proof
  convergent_exact_couple_g_isomorphism
  (serre_convergence (fiber f) Y s₀ H)
Proof. intro p q, reflexivity end
Proof. intro n, apply unreduced_cohomology_isomorphism, exact !sigma_fiber_equiv^-1ᵉ end
  qed

Definition serre_spectral_sequence_map :
  convergent_spectral_sequence_g (fun p q => uopH^p[(b : B), uH^q[fiber f b, Y]]) (fun n => uH^n[X, Y]).
Proof.
  apply convergent_spectral_sequence_of_exact_couple (serre_convergence_map f Y s₀ H),
  { intro n, exact add.comm (s₀ - -n) (-s₀) @ !neg_add_cancel_left @ !neg_neg },
  { reflexivity }
Defined.

Definition serre_convergence_of_is_conn (H2 : is_conn 1 B) :
  (fun p q => uoH^p[B, uH^q[F b₀, Y]]) ⟹ᵍ (fun n => uH^n[Σ(b : B), F b, Y]).
  proof
  convergent_exact_couple_g_isomorphism
  (serre_convergence F Y s₀ H)
Proof. intro p q, exact @uopH_isomorphism_uoH_of_is_conn (pointed.MK B b₀) _ _ H2  end
Proof. intro n, reflexivity end
  qed

Definition serre_spectral_sequence_of_is_conn (H2 : is_conn 1 B) :
  convergent_spectral_sequence_g (fun p q => uoH^p[B, uH^q[F b₀, Y]]) (fun n => uH^n[Σ(b : B), F b, Y]).
Proof.
  apply convergent_spectral_sequence_of_exact_couple (serre_convergence_of_is_conn b₀ F Y s₀ H H2),
  { intro n, exact add.comm (s₀ - -n) (-s₀) @ !neg_add_cancel_left @ !neg_neg },
  { reflexivity }
Defined.

Definition serre_convergence_map_of_is_conn (H2 : is_conn 1 B) :
  (fun p q => uoH^p[B, uH^q[fiber f b₀, Y]]) ⟹ᵍ (fun n => uH^n[X, Y]).
  proof
  convergent_exact_couple_g_isomorphism
  (serre_convergence_of_is_conn b₀ (fiber f) Y s₀ H H2)
Proof. intro p q, reflexivity end
Proof. intro n, apply unreduced_cohomology_isomorphism, exact !sigma_fiber_equiv^-1ᵉ end
  qed

Definition serre_spectral_sequence_map_of_is_conn' (H2 : is_conn 1 B) :
  convergent_spectral_sequence_g (fun p q => uoH^p[B, uH^q[fiber f b₀, Y]]) (fun n => uH^n[X, Y]).
Proof.
  apply convergent_spectral_sequence_of_exact_couple (serre_convergence_map_of_is_conn b₀ f Y s₀ H H2),
  { intro n, exact add.comm (s₀ - -n) (-s₀) @ !neg_add_cancel_left @ !neg_neg },
  { reflexivity }
Defined.

Definition serre_spectral_sequence_map_of_is_conn (H2 : is_conn 1 B) :
  convergent_spectral_sequence_g (fun p q => uoH^p[B, uH^q[fiber f b₀, Y]]) (fun n => uH^n[X, Y]).
  (convergent_spectral_sequence,
  deg_d . fun (r : ℕ) => (r + 2, -(r + 1)),
  lb    . fun x => -s₀,
  serre_spectral_sequence_map_of_is_conn' b₀ f Y s₀ H H2)

  omit H
Definition is_normal_serre_spectral_sequence_map_of_is_conn (H' : is_strunc 0 Y)
  (H2 : is_conn 1 B) :
  spectral_sequence.is_normal (serre_spectral_sequence_map_of_is_conn b₀ f Y 0 H' H2).
Proof.
  apply spectral_sequence.is_normal.mk,
  { intro p q Hp, exact is_contr_ordinary_cohomology_of_neg _ _ Hp },
  { intro p q Hp, apply is_contr_ordinary_cohomology,
  apply is_contr_cohomology_of_is_contr_spectrum,
  exact is_contr_of_is_strunc _ _ H' Hp },
  { intro r, reflexivity },
Defined.


Defined. serre

Defined. spectrum
