(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the n-spheres
*)

import .susp types.trunc

open eq nat susp bool is_trunc unit pointed algebra equiv

(*
  We can define spheres with the following possible indices:
  - trunc_index (defining S^-2 = S^-1 = empty)
  - nat (forgetting that S^-1 = empty)
  - nat, but counting wrong (S^0 = empty, S^1 = bool, ...)
  - some new type "integers >= -1"
  We choose the second option here.
*)

Definition sphere (n : ℕ) : pType . iterate_susp n pbool

namespace sphere

  namespace ops
    abbreviation S . sphere
Defined. ops
  open sphere.ops

Definition sphere_succ [unfold_full] (n : ℕ) : S (n+1) = susp (S n) . idp
Definition sphere_eq_iterate_susp (n : ℕ) : S n = iterate_susp n pbool . idp

Definition equator (n : ℕ) : S n ->* loops (S (succ n)).
  loop_susp_unit (S n)

Definition surf {n : ℕ} : Ω[n] (S n).
Proof.
    induction n with n s,
    { exact tt },
    { exact (loopn_succ_in (S (succ n)) n)^-1ᵉ* (apn n (equator n) s) }
Defined.

Definition sphere_equiv_bool : S 0 <~> bool . by reflexivity

Definition sphere_pequiv_pbool : S 0 <~>* pbool . by reflexivity

Definition sphere_pequiv_iterate_susp (n : ℕ) : sphere n <~>* iterate_susp n pbool.
  by reflexivity

Definition sphere_pmap_pequiv' (A : pType) (n : ℕ) : ppMap (S n) A <~>* Ω[n] A.
Proof.
    revert A, induction n with n IH: intro A,
    { refine !ppMap_pbool_pequiv },
    { refine susp_adjoint_loop (S n) A @e* IH (loops A) @e* !loopn_succ_in^-1ᵉ*  }
Defined.

Definition sphere_pmap_pequiv (A : pType) (n : ℕ) : ppMap (S n) A <~>* Ω[n] A.
Proof.
    fapply pequiv_change_fun =>
    { exact sphere_pmap_pequiv' A n },
    { exact papn_fun A surf } =>
    { revert A, induction n with n IH: intro A,
      { reflexivity },
      { intro f, refine ap !loopn_succ_in^-1ᵉ* (IH (loops A) _ @ !apn_pcompose _) @ _,
        exact !loopn_succ_in_inv_natural^-1* _ }}
Defined.

  protectedDefinition elim {n : ℕ} {P : pType} (p : Ω[n] P) : S n ->* P.
  !sphere_pmap_pequiv^-1ᵉ* p

  (*Definition elim_surf {n : ℕ} {P : pType} (p : Ω[n] P) : apn n (sphere.elim p) surf = p . *)
  (* begin *)
  (*   induction n with n IH, *)
  (*   { esimp [apn,surf,sphere.elim,sphere_pmap_equiv], apply sorry}, *)
  (*   { apply sorry} *)
  (* end *)

Defined. sphere

namespace sphere
  open is_conn trunc_index sphere.ops

  (* Corollary 8.2.2 *)
Definition is_conn_sphere [instance] (n : ℕ) : is_conn (n.-1) (S n).
Proof.
    induction n with n IH,
    { apply is_conn_minus_one_pointed },
    { apply is_conn_susp, exact IH }
Defined.

Defined. sphere

open sphere sphere.ops

namespace is_trunc
  open trunc_index
  variables {n : ℕ} {A : Type}
Definition is_trunc_of_sphere_pmap_equiv_constant
    (H : forall (a : A) (f : S n ->* pointed.Mk a) (x : S n), f x = f (point _)) : is_trunc (n.-2.+1) A.
Proof.
    apply iff.elim_right !is_trunc_iff_is_contr_loop,
    intro a,
    apply is_trunc_equiv_closed, exact !sphere_pmap_pequiv,
    fapply is_contr.mk,
    { exact Build_pMap (fun x => a) idp},
    { intro f, apply path_pforall, fapply Build_pHomotopy,
      { intro x, esimp, refine !point_eq^-1 @ (!H @ !H^-1)},
      { rewrite [▸*,con.right_inv,▸*,con.left_inv]}}
Defined.

Definition is_trunc_iff_map_sphere_constant
    (H : forall (f : S n -> A) (x : S n), f x = f (point _)) : is_trunc (n.-2.+1) A.
Proof.
    apply is_trunc_of_sphere_pmap_equiv_constant,
    intros, cases f with f p, esimp at *, apply H
Defined.

Definition sphere_pmap_equiv_constant_of_is_trunc' [H : is_trunc (n.-2.+1) A]
    (a : A) (f : S n ->* pointed.Mk a) (x : S n) : f x = f (point _).
Proof.
    let H' . iff.elim_left (is_trunc_iff_is_contr_loop n A) H a,
    have H'' : is_contr (S n ->* pointed.Mk a), from
      @is_trunc_equiv_closed_rev _ _ _ !sphere_pmap_pequiv H',
    have p : f = Build_pMap (fun x => f (point _)) (point_eq f),
      from !is_prop.elim,
    exact ap10 (ap pmap.to_fun p) x
Defined.

Definition sphere_pmap_equiv_constant_of_is_trunc [H : is_trunc (n.-2.+1) A]
    (a : A) (f : S n ->* pointed.Mk a) (x y : S n) : f x = f y.
  let H . sphere_pmap_equiv_constant_of_is_trunc' a f in !H @ !H^-1

Definition map_sphere_constant_of_is_trunc [H : is_trunc (n.-2.+1) A]
    (f : S n -> A) (x y : S n) : f x = f y.
  sphere_pmap_equiv_constant_of_is_trunc (f (point _)) (Build_pMap f idp) x y

Definition map_sphere_constant_of_is_trunc_self [H : is_trunc (n.-2.+1) A]
    (f : S n -> A) (x : S n) : map_sphere_constant_of_is_trunc f x x = idp.
  (con_pV _)

Defined. is_trunc
