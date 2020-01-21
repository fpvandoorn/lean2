(*
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

The Freudenthal Suspension Theorem
*)

import homotopy.wedge homotopy.circle

open eq is_conn is_trunc pointed susp nat pi equiv is_equiv trunc fiber trunc_index

namespace freudenthal section

  parameters {A : pType} {n : ℕ} [is_conn n A]

  (*
    This proof is ported from Agda
    This is the 95% version of the Freudenthal Suspension Theorem, which means that we don't
    prove that loop_susp_unit : A ->* Ω(susp A) is 2n-connected (if A is n-connected),
    but instead we only prove that it induces an equivalence on the first 2n homotopy groups.
  *)

  privateDefinition up (a : A) : north = north :> susp A.
  loop_susp_unit A a

Definition code_merid : A -> ptrunc (n + n) A -> ptrunc (n + n) A.
Proof.
    have is_conn n (ptrunc (n + n) A), from !is_conn_trunc,
    refine @wedge_extension.ext _ _ n n _ _ (fun x y => ttrunc (n + n) A) _ _ _ _,
    { intros, apply is_trunc_trunc}, (* this subgoal might become unnecessary if *)
                                     (* type class inference catches it *)
    { exact tr},
    { exact id},
    { reflexivity}
Defined.

Definition code_merid_β_left (a : A) : code_merid a (point _) = tr a.
  by apply wedge_extension.β_left

Definition code_merid_β_right (b : ptrunc (n + n) A) : code_merid (point _) b = b.
  by apply wedge_extension.β_right

Definition code_merid_coh : code_merid_β_left (point _) = code_merid_β_right (point _).
Proof.
    symmetry, apply eq_of_inv_con_eq_idp, apply wedge_extension.coh
Defined.

Definition is_equiv_code_merid (a : A) : is_equiv (code_merid a).
Proof.
    have forall a, is_trunc n.-2.+1 (is_equiv (code_merid a)),
      from fun a => is_trunc_of_le _ !minus_one_le_succ,
    refine is_conn.elim (n.-1) _ _ a,
    { esimp, exact homotopy_closed id (homotopy.symm (code_merid_β_right))}
Defined.

Definition code_merid_equiv (a : A) : trunc (n + n) A <~> trunc (n + n) A.
  equiv.mk _ (is_equiv_code_merid a)

Definition code_merid_inv_pt (x : trunc (n + n) A) : (code_merid_equiv (point _))^-1 x = x.
Proof.
    refine ap010 @(is_equiv.inv _) _ x @ _,
    { exact homotopy_closed id (homotopy.symm code_merid_β_right)},
    { apply is_conn.elim_β},
    { reflexivity}
Defined.

Definition code : susp A -> Type.
  susp.elim_type (trunc (n + n) A) (trunc (n + n) A) code_merid_equiv

Definition is_trunc_code (x : susp A) : is_trunc (n + n) (code x).
Proof.
    induction x with a: esimp,
    { exact _},
    { exact _},
    { apply is_prop.elimo}
Defined.
  local attribute is_trunc_code [instance]

Definition decode_north : code north -> trunc (n + n) (north = north :> susp A).
  trunc_functor (n + n) up

Definition decode_north_pt : decode_north (tr (point _)) = tr idp.
  ap tr (con_pV _)

Definition decode_south : code south -> trunc (n + n) (north = south :> susp A).
  trunc_functor (n + n) merid

Definition encode' {x : susp A} (p : north = x) : code x.
  transport code p (tr (point _))

Definition encode {x : susp A} (p : trunc (n + n) (north = x)) : code x.
Proof.
    induction p with p,
    exact transport code p (tr (point _))
Defined.

Definition encode_decode_north (c : code north) : encode (decode_north c) = c.
Proof.
    have H : forall c, is_trunc (n + n) (encode (decode_north c) = c), from _,
    esimp at *,
    induction c with a,
    rewrite [↑[encode, decode_north, up, code], con_tr, elim_type_merid, ▸*,
             code_merid_β_left, elim_type_merid_inv, ▸*, code_merid_inv_pt]
Defined.

Definition decode_coh_f (a : A) : tr (up (point _)) =[merid a] decode_south (code_merid a (tr (point _))).
Proof.
    refine _ @op ap decode_south (code_merid_β_left a)^-1,
    apply trunc_pathover,
    apply eq_pathover_constant_left_id_right,
    apply square_of_eq,
    exact whisker_right (merid a) (con_pV _)
Defined.

Definition decode_coh_g (a' : A) : tr (up a') =[merid (point _)] decode_south (code_merid (point _) (tr a')).
Proof.
    refine _ @op ap decode_south (code_merid_β_right (tr a'))^-1,
    apply trunc_pathover,
    apply eq_pathover_constant_left_id_right,
    apply square_of_eq, refine !inv_con_cancel_right @ (concat_1p _)^-1
Defined.

Definition decode_coh_lem {A : Type} {a a' : A} (p : a = a')
    : whisker_right p (con.right_inv p) = inv_con_cancel_right p p @ (idp_con p)^-1.
  by induction p; reflexivity

Definition decode_coh (a : A) : decode_north =[merid a] decode_south.
Proof.
    apply arrow_pathover_left, intro c,
    induction c with a',
    rewrite [↑code, elim_type_merid],
    refine @wedge_extension.ext _ _ n n _ _ (fun a a' => tr (up a') =[merid a] decode_south
    (to_fun (code_merid_equiv a) (tr a'))) _ _ _ _ a a' =>
    { intros, apply is_trunc_pathover, apply is_trunc_succ, apply is_trunc_trunc},
    { exact decode_coh_f},
    { exact decode_coh_g},
    { clear a a', unfold [decode_coh_f, decode_coh_g], refine ap011 concato_eq _ _,
      { refine ap (fun p => trunc_pathover (eq_pathover_constant_left_id_right (square_of_eq p))) _,
        apply decode_coh_lem},
      { apply ap (fun p => ap decode_south p^-1), apply code_merid_coh}}
Defined.

Definition decode {x : susp A} (c : code x) : trunc (n + n) (north = x).
Proof.
    induction x with a,
    { exact decode_north c},
    { exact decode_south c},
    { exact decode_coh a}
Defined.

Definition decode_encode {x : susp A} (p : trunc (n + n) (north = x)) : decode (encode p) = p.
Proof.
    induction p with p, induction p, esimp, apply decode_north_pt
Defined.

  parameters (A n)
Definition equiv' : trunc (n + n) A <~> trunc (n + n) (loops (susp A)).
  equiv.MK decode_north encode decode_encode encode_decode_north

Definition pequiv' : ptrunc (n + n) A <~>* ptrunc (n + n) (loops (susp A)).
  pequiv_of_equiv equiv' decode_north_pt

  (* We don't prove this: *)
  (*Definition freudenthal_suspension : is_conn_fun (n+n) (loop_susp_unit A) . sorry *)

Defined. end freudenthal

open algebra group
Definition freudenthal_pequiv (A : pType) {n k : ℕ} [is_conn n A] (H : k ≤ 2 * n)
  : ptrunc k A <~>* ptrunc k (loops (susp A)).
have H' : k ≤[ℕ₋₂] n + n,
  by rewrite [mul.comm at H, -algebra.zero_add n at {1}]; exact of_nat_le_of_nat H,
ptrunc_pequiv_ptrunc_of_le H' (freudenthal.pequiv' A n)

Definition freudenthal_equiv {A : pType} {n k : ℕ} [is_conn n A] (H : k ≤ 2 * n)
  : trunc k A <~> trunc k (loops (susp A)).
freudenthal_pequiv A H

Definition freudenthal_homotopy_group_pequiv (A : pType) {n k : ℕ} [is_conn n A] (H : k ≤ 2 * n)
  : forall [k + 1] (susp A) <~>* forall [k] A .
calc
  forall [k + 1] (susp A) <~>* forall [k] (loops (susp A)) : homotopy_group_succ_in (susp A) k
    ... <~>* Ω[k] (ptrunc k (loops (susp A)))  : homotopy_group_pequiv_loop_ptrunc k (loops (susp A))
    ... <~>* Ω[k] (ptrunc k A)             : loopn_pequiv_loopn k (freudenthal_pequiv A H)
    ... <~>* forall [k] A                        : (homotopy_group_pequiv_loop_ptrunc k A)^-1ᵉ*

Definition freudenthal_homotopy_group_isomorphism (A : pType) {n k : ℕ} [is_conn n A]
  (H : k + 1 ≤ 2 * n) : forall g[k+2] (susp A) <~>g forall g[k + 1] A.
Proof.
  fapply isomorphism_of_equiv,
  { exact equiv_of_pequiv (freudenthal_homotopy_group_pequiv A H)},
  { intro g h,
    refine _ @ !homotopy_group_pequiv_loop_ptrunc_inv_con,
    apply ap !homotopy_group_pequiv_loop_ptrunc^-1ᵉ*,
    refine ap (loopn_pequiv_loopn _ _) _ @ !loopn_pequiv_loopn_con,
    refine ap !homotopy_group_pequiv_loop_ptrunc _ @ !homotopy_group_pequiv_loop_ptrunc_con,
    apply homotopy_group_succ_in_con}
Defined.

Definition to_pmap_freudenthal_pequiv {A : pType} (n k : ℕ) [is_conn n A] (H : k ≤ 2 * n)
    : freudenthal_pequiv A H ==* ptrunc_functor k (loop_susp_unit A).
Proof.
    fapply Build_pHomotopy,
    { intro x, induction x with a, reflexivity },
    { refine (concat_1p _) @ _, refine _ @ ap02 _ (concat_1p _)^-1, refine _ @ !ap_compose, apply ap_compose }
Defined.

Definition ptrunc_elim_freudenthal_pequiv {A B : pType} (n k : ℕ) [is_conn n A] (H : k ≤ 2 * n)
    (f : A ->* loops B) [is_trunc (k.+1) (B)] :
    ptrunc.elim k (Ω-> (susp_elim f)) o* freudenthal_pequiv A H ==* ptrunc.elim k f.
Proof.
    refine pwhisker_left _ !to_pmap_freudenthal_pequiv @* _,
    refine !ptrunc_elim_ptrunc_functor @* _ =>
    exact ptrunc_elim_phomotopy k !ap1_susp_elim,
Defined.

namespace susp

Definition iterate_susp_stability_pequiv_of_is_conn_0 (A : pType) {k n : ℕ} [is_conn 0 A]
    (H : k ≤ 2 * n) : forall [k + 1] (iterate_susp (n + 1) A) <~>* forall [k] (iterate_susp n A).
  have is_conn n (iterate_susp n A), by rewrite [-zero_add n]; exact _,
  freudenthal_homotopy_group_pequiv (iterate_susp n A) H

Definition iterate_susp_stability_isomorphism_of_is_conn_0 (A : pType) {k n : ℕ} [is_conn 0 A]
    (H : k + 1 ≤ 2 * n) : forall g[k+2] (iterate_susp (n + 1) A) <~>g forall g[k+1] (iterate_susp n A).
  have is_conn n (iterate_susp n A), by rewrite [-zero_add n]; exact _,
  freudenthal_homotopy_group_isomorphism (iterate_susp n A) H

Definition stability_helper1 {k n : ℕ} (H : k + 2 ≤ 2 * n) : k ≤ 2 * pred n.
Proof.
    rewrite [mul_pred_right], change pred (pred (k + 2)) ≤ pred (pred (2 * n)),
    apply pred_le_pred, apply pred_le_pred, exact H
Defined.

Definition stability_helper2 (A : pType) {k n : ℕ} (H : k + 2 ≤ 2 * n) :
    is_conn (pred n) (iterate_susp n A).
  have forall (n : ℕ), n = -1 + (n + 1),
Proof. intro n, induction n with n IH, reflexivity, exact ap succ IH end,
Proof.
    cases n with n,
    { exfalso, exact not_succ_le_zero _ H },
    { esimp, rewrite [this n], exact is_conn_iterate_susp -1 _ A }
Defined.

Definition iterate_susp_stability_pequiv (A : pType) {k n : ℕ}
    (H : k + 2 ≤ 2 * n) : forall [k + 1] (iterate_susp (n + 1) A) <~>* forall [k] (iterate_susp n A).
  have is_conn (pred n) (iterate_susp n A), from stability_helper2 A H,
  freudenthal_homotopy_group_pequiv (iterate_susp n A) (stability_helper1 H)

Definition iterate_susp_stability_isomorphism (A : pType) {k n : ℕ}
    (H : k + 3 ≤ 2 * n) : forall g[k+2] (iterate_susp (n + 1) A) <~>g forall g[k+1] (iterate_susp n A).
  have is_conn (pred n) (iterate_susp n A), from @stability_helper2 A (k+1) n H,
  freudenthal_homotopy_group_isomorphism (iterate_susp n A) (stability_helper1 H)

Definition iterated_freudenthal_pequiv (A : pType) {n k m : ℕ} [HA : is_conn n A] (H : k ≤ 2 * n)
    : ptrunc k A <~>* ptrunc k (Ω[m] (iterate_susp m A)).
Proof.
    revert A n k HA H, induction m with m IH: intro A n k HA H,
    { reflexivity },
    { have H2 : succ k ≤ 2 * succ n,
      from calc
        succ k ≤ succ (2 * n) : succ_le_succ H
           ... ≤ 2 * succ n   : self_le_succ,
      exact calc
        ptrunc k A <~>* ptrunc k (loops (susp A))   : freudenthal_pequiv A H
          ... <~>* loops (ptrunc (succ k) (susp A)) : loop_ptrunc_pequiv
          ... <~>* loops (ptrunc (succ k) (Ω[m] (iterate_susp m (susp A)))) :
                   loop_pequiv_loop (IH (susp A) (succ n) (succ k) _ H2)
          ... <~>* ptrunc k (Ω[succ m] (iterate_susp m (susp A))) : loop_ptrunc_pequiv
          ... <~>* ptrunc k (Ω[succ m] (iterate_susp (succ m) A)) :
                   ptrunc_pequiv_ptrunc _ (loopn_pequiv_loopn _ !iterate_susp_succ_in)}
Defined.

Defined. susp
