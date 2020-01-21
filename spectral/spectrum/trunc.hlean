(*
Copyright (c) 2017 Floris van Doorn and Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz

Truncatedness and truncation of spectra
*)

import .basic
open int trunc eq is_trunc lift unit pointed equiv is_equiv algebra EM trunc_index

namespace spectrum

(* interactions of ptrunc / trunc with maxm2 *)
Definition ptrunc_maxm2_change_int {k l : ℤ} (p : k = l) (X : pType)
  : ptrunc (maxm2 k) X <~>* ptrunc (maxm2 l) X :=
ptrunc_change_index (ap maxm2 p) X

Definition is_trunc_maxm2_change_int {k l : ℤ} (X : pType) (p : k = l)
  : is_trunc (maxm2 k) X -> is_trunc (maxm2 l) X :=
by induction p; exact id

Definition is_trunc_maxm2_loop {k : ℤ} {A : pType} (H : is_trunc (maxm2 (k+1)) A) :
  is_trunc (maxm2 k) (loops A) :=
Proof.
  induction k with k k,
    apply is_trunc_loop, exact H,
  apply is_contr_loop,
  cases k with k,
  { exact H },
  { apply is_trunc_succ, apply is_trunc_succ, exact H }
Defined.

Definition loop_ptrunc_maxm2_pequiv {k : ℤ} {l : ℕ₋₂} (p : maxm2 (k+1) = l) (X : pType) :
  loops (ptrunc l X) <~>* ptrunc (maxm2 k) (loops X) :=
Proof.
  induction p,
  induction k with k k,
  { exact loop_ptrunc_pequiv k X },
  { refine pequiv_of_is_contr _ _ _ !is_trunc_trunc,
    apply is_contr_loop,
    cases k with k,
    { change is_set (trunc 0 X), apply _ },
    { change is_set (trunc -2 X), apply _ }}
Defined.

Definition loop_ptrunc_maxm2_pequiv_ptrunc_elim' {k : ℤ} {l : ℕ₋₂} (p : maxm2 (k+1) = l)
  {A B : pType} (f : A ->* B) {H : is_trunc l B} :
  Ω-> (ptrunc.elim l f) o* (loop_ptrunc_maxm2_pequiv p A)^-1ᵉ* ==*
  @ptrunc.elim (maxm2 k) _ _ (is_trunc_maxm2_loop (is_trunc_of_eq p^-1 H)) (Ω-> f) :=
Proof.
  induction p, induction k with k k,
  { refine pwhisker_right _ (ap1_phomotopy _) @* @(ap1_ptrunc_elim k f) H,
    apply ptrunc_elim_phomotopy2, reflexivity },
  { apply phomotopy_of_is_contr_cod_pmap, exact is_trunc_maxm2_loop H }
Defined.

Definition loop_ptrunc_maxm2_pequiv_ptrunc_elim {k : ℤ} {l : ℕ₋₂} (p : maxm2 (k+1) = l)
  {A B : pType} (f : A ->* B) {H1 : is_trunc ((maxm2 k).+1) B } {H2 : is_trunc l B} :
  Ω-> (ptrunc.elim l f) o* (loop_ptrunc_maxm2_pequiv p A)^-1ᵉ* ==* ptrunc.elim (maxm2 k) (Ω-> f) :=
Proof.
  induction p, induction k with k k: esimp at H1,
  { refine pwhisker_right _ (ap1_phomotopy _) @* ap1_ptrunc_elim k f,
    apply ptrunc_elim_phomotopy2, reflexivity },
  { apply phomotopy_of_is_contr_cod }
Defined.

Definition loop_ptrunc_maxm2_pequiv_ptr {k : ℤ} {l : ℕ₋₂} (p : maxm2 (k+1) = l) (A : pType) :
  Ω-> (ptr l A) ==* (loop_ptrunc_maxm2_pequiv p A)^-1ᵉ* o* ptr (maxm2 k) (loops A) :=
Proof.
  induction p, induction k with k k,
  { exact ap1_ptr k A },
  { apply phomotopy_pinv_left_of_phomotopy, apply phomotopy_of_is_contr_cod_pmap,
    apply is_trunc_trunc }
Defined.

Definition is_trunc_of_is_trunc_maxm2 (k : ℤ) (X : Type)
  : is_trunc (maxm2 k) X -> is_trunc (max0 k) X :=
fun H => @is_trunc_of_le X _ _ (maxm2_le_maxm0 k) H

Definition ptrunc_maxm2_pred {n m : ℤ} (A : pType) (p : n - 1 = m) :
  ptrunc (maxm2 m) A <~>* ptrunc (trunc_index.pred (maxm2 n)) A :=
Proof.
  cases n with n, cases n with n, apply pequiv_of_is_contr,
        induction p, apply is_trunc_trunc,
      apply is_contr_ptrunc_minus_one,
    exact ptrunc_change_index (ap maxm2 (p^-1 @ !add_sub_cancel)) A,
  exact ptrunc_change_index (ap maxm2 p^-1) A
Defined.

Definition ptrunc_maxm2_pred_nat {n : ℕ} {m l : ℤ} (A : pType)
  (p : nat.succ n = l) (q : pred l = m) (r : maxm2 m = trunc_index.pred (maxm2 (nat.succ n))) :
  @ptrunc_maxm2_pred (nat.succ n) m A (ap pred p @ q) ==* ptrunc_change_index r A :=
Proof.
  have ap maxm2 ((ap pred p @ q)^-1 @ add_sub_cancel n 1) = r, from !is_set.elim,
  induction this, reflexivity
Defined.

(* truncatedness of spectra *)
Definition is_strunc (k : ℤ) (E : spectrum) : Type :=
forall (n : ℤ), is_trunc (maxm2 (k + n)) (E n)

Definition is_strunc_change_int {k l : ℤ} (E : spectrum) (p : k = l)
  : is_strunc k E -> is_strunc l E :=
Proof. induction p, exact id end

Definition is_strunc_of_le {k l : ℤ} (E : spectrum) (H : k ≤ l)
  : is_strunc k E -> is_strunc l E :=
Proof.
  intro T, intro n, exact is_trunc_of_le (E n) (maxm2_monotone (algebra.add_le_add_right H n)) _
Defined.

Definition is_strunc_pequiv_closed {k : ℤ} {E F : spectrum} (H : forall n, E n <~>* F n)
  (H2 : is_strunc k E) : is_strunc k F :=
fun n => is_trunc_equiv_closed (maxm2 (k + n)) (H n) _

Definition is_strunc_sunit (n : ℤ) : is_strunc n sunit :=
Proof.
  intro k, apply is_trunc_lift, apply is_trunc_unit
Defined.

Definition is_contr_of_is_strunc (n : ℤ) {m : ℤ} (E : spectrum) (H : is_strunc n E)
  (Hmn : m < -n) : is_contr (E m) :=
Proof.
  refine transport (fun n => is_trunc n (E m)) _ (H m),
  apply maxm2_eq_minus_two,
  exact lt_of_lt_of_le (add_lt_add_left Hmn n) (le_of_eq !add.right_inv)
Defined.

open option
Definition is_strunc_add_point_spectrum {X : Type} {Y : X -> spectrum} {s₀ : ℤ}
  (H : forall x, is_strunc s₀ (Y x)) : forall (x : X₊), is_strunc s₀ (add_point_spectrum Y x)
| (some x) := proof H x qed
| none     := begin intro k, apply is_trunc_lift, apply is_trunc_unit end

Definition is_strunc_EM_spectrum (G : AbGroup)
  : is_strunc 0 (EM_spectrum G) :=
Proof.
  intro n, induction n with n n,
  {     apply is_trunc_maxm2_change_int (EM G n) (zero_add n)^-1,
    apply is_trunc_EM },
  { change is_contr (EM_spectrum G (-[1+n])),
    induction n with n IH,
    {       apply is_contr_loop, exact is_trunc_EM G 0 },
    {       apply is_trunc_loop, apply is_trunc_succ, exact IH }}
Defined.

Definition trivial_shomotopy_group_of_is_strunc (E : spectrum)
  {n k : ℤ} (K : is_strunc n E) (H : n < k)
  : is_contr (forall ₛ[k] E) :=
let m := n + (2 - k) in
have I : m < 2, from
  calc
    m = (2 - k) + n : int.add_comm n (2 - k)
  ... < (2 - k) + k : add_lt_add_left H (2 - k)
  ... = 2           : sub_add_cancel 2 k,
@trivial_homotopy_group_of_is_trunc (E (2 - k)) (max0 m) 2
  (is_trunc_of_is_trunc_maxm2 m (E (2 - k)) (K (2 - k)))
  (nat.succ_le_succ (max0_le_of_le (le_sub_one_of_lt I)))

(* truncation of spectra *)
Definition strunc (k : ℤ) (E : spectrum) : spectrum :=
spectrum.MK (fun (n : ℤ) => ptrunc (maxm2 (k + n)) (E n))
            (fun (n : ℤ) => ptrunc_pequiv_ptrunc (maxm2 (k + n)) (equiv_glue E n)
              @e* (loop_ptrunc_maxm2_pequiv (ap maxm2 (add.assoc k n 1)) (E (n+1)))^-1ᵉ*)

Definition strunc_change_int {k l : ℤ} (E : spectrum) (p : k = l) :
  strunc k E ->ₛ strunc l E :=
Proof. induction p, reflexivity end

Definition is_strunc_strunc (k : ℤ) (E : spectrum)
  : is_strunc k (strunc k E) :=
fun n => is_trunc_trunc (maxm2 (k + n)) (E n)

Definition is_strunc_strunc_pred (X : spectrum) (k : ℤ) : is_strunc k (strunc (k - 1) X) :=
fun n => @(is_trunc_of_le _ (maxm2_monotone (add_le_add_right (sub_one_le k) n))) !is_strunc_strunc

Definition is_strunc_strunc_of_is_strunc (k : ℤ) {l : ℤ} {E : spectrum} (H : is_strunc l E)
  : is_strunc l (strunc k E) :=
fun n => !is_trunc_trunc_of_is_trunc

Definition str (k : ℤ) (E : spectrum) : E ->ₛ strunc k E :=
smap.mk (fun n => ptr (maxm2 (k + n)) (E n))
  abstract begin
    intro n,
    apply psquare_of_phomotopy,
    refine !passoc @* pwhisker_left _ !ptr_natural @* _,
    refine !passoc^-1* @* pwhisker_right _ !loop_ptrunc_maxm2_pequiv_ptr^-1*,
Defined. end

Definition strunc_elim {k : ℤ} {E F : spectrum} (f : E ->ₛ F)
  (H : is_strunc k F) : strunc k E ->ₛ F :=
smap.mk (fun n => ptrunc.elim (maxm2 (k + n)) (f n))
  abstract begin
    intro n,
    apply psquare_of_phomotopy,
    symmetry,
    refine !passoc^-1* @* pwhisker_right _ !loop_ptrunc_maxm2_pequiv_ptrunc_elim' @* _,
    refine @(ptrunc_elim_ptrunc_functor _ _ _) _ @* _ =>
    refine _ @* @(ptrunc_elim_pcompose _ _ _) _ _,
      apply is_trunc_maxm2_loop,
      refine is_trunc_of_eq _ (H (n+1)), exact ap maxm2 (add.assoc k n 1)^-1,
    apply ptrunc_elim_phomotopy2,
    apply phomotopy_of_psquare,
    apply ptranspose,
    apply smap.glue_square
Defined. end

Definition strunc_functor (k : ℤ) {E F : spectrum} (f : E ->ₛ F) :
  strunc k E ->ₛ strunc k F :=
strunc_elim (str k F oₛ f) (is_strunc_strunc k F)

(* truncated spectra *)
structure truncspectrum (n : ℤ) :=
  (carrier : spectrum)
  (struct : is_strunc n carrier)

notation n `-spectrum` := truncspectrum n



Definition genspectrum_of_truncspectrum [coercion] (n : ℤ) : n-spectrum -> gen_spectrum +ℤ :=
fun E => truncspectrum.carrier E

(* Comment (by Floris):

  I think we should really not bundle truncated spectra up,
  unless we are interested in the type of truncated spectra (e.g. when proving n-spectrum <~> ...).
  Properties of truncated a spectrum should just be stated with two assumptions
  (X : spectrum) (H : is_strunc n X)
*)

(* truncatedness of spi and sp_cotensor assuming the domain has a level of connectedness *)
section

  open is_conn

Definition is_conn_maxm1_of_maxm2 (A : pType) (n : ℤ)
    : is_conn (maxm2 n) A -> is_conn (maxm1m1 n).+1 A :=
Proof.
    intro H, induction n with n n,
    { exact H },
    { exact is_conn_minus_one A (tr (point _)) }
Defined.

Definition is_trunc_maxm2_of_maxm1 (A : pType) (n : ℤ)
    : is_trunc (maxm1m1 n).+1 A -> is_trunc (maxm2 n) A :=
Proof.
    intro H, induction n with n n,
    { exact H},
    { apply is_contr_of_merely_prop,
      { exact H },
      { exact tr (point _) } }
Defined.

  variables (A : pType) (n : ℤ) [H : is_conn (maxm2 n) A]
  include H

Definition is_trunc_maxm2_ppi (k l : ℤ) (H3 : l ≤ n+1+k) (P : A -> pType)
    (H2 : forall a, is_trunc (maxm2 l) (P a)) : is_trunc (maxm2 k) (ppforall (a : A), P a) :=
  is_trunc_maxm2_of_maxm1 (ppforall (a : A), P a) k
    (@is_trunc_ppi_of_is_conn A (maxm1m1 n) (is_conn_maxm1_of_maxm2 A n H) (maxm1m1 k) _
      (le.trans (maxm2_monotone H3) (maxm2_le n k)) P H2)

Definition is_strunc_spi_of_is_conn (k l : ℤ) (H3 : l ≤ n+1+k) (P : A -> spectrum)
    (H2 : forall a, is_strunc l (P a)) : is_strunc k (spi A P) :=
Proof.
    intro m, unfold spi,
    exact is_trunc_maxm2_ppi A n (k+m) _ (le.trans (add_le_add_right H3 _)
            (le_of_eq (add.assoc (n+1) k m))) (fun a => P a m) (fun a => H2 a m)
Defined.

Defined.

Definition is_strunc_spi_of_le {A : pType} (k n : ℤ) (H : n ≤ k) (P : A -> spectrum)
  (H2 : forall a, is_strunc n (P a)) : is_strunc k (spi A P) :=
Proof.
  assert K : n ≤ -[1+ 0] + 1 + k,
  { krewrite (int.zero_add k), exact H },
  { exact @is_strunc_spi_of_is_conn A (-[1+ 0]) (is_conn.is_conn_minus_two A) k _ K P H2 }
Defined.

Definition is_strunc_spi {A : pType} (n : ℤ) (P : A -> spectrum) (H : forall a, is_strunc n (P a))
  : is_strunc n (spi A P) :=
is_strunc_spi_of_le n n !le.refl P H

Definition is_strunc_sp_cotensor (n : ℤ) (A : pType) {Y : spectrum} (H : is_strunc n Y)
  : is_strunc n (sp_cotensor A Y) :=
is_strunc_pequiv_closed (fun n => !pppi_pequiv_ppMap) (is_strunc_spi n (fun a => Y) (fun a => H))

Definition is_strunc_sp_ucotensor (n : ℤ) (A : Type) {Y : spectrum} (H : is_strunc n Y)
  : is_strunc n (sp_ucotensor A Y) :=
fun k => !pi.is_trunc_arrow

Defined. spectrum
