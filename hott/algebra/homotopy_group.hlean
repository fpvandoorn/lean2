(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

homotopy groups of a pointed space
*)

import .trunc_group types.trunc .group_theory types.nat.hott

open nat eq pointed trunc is_trunc algebra group function equiv unit is_equiv nat

(* TODO: consistently make n an argument before A *)
(* TODO: rename cghomotopy_group to aghomotopy_group *)
(* TODO: rename homotopy_group_functor_compose to homotopy_group_functor_pcompose *)
namespace eq

Definition inf_pgroup_loop [instance] (A : pType) : inf_pgroup (loops A).
  inf_pgroup.mk concat con.assoc inverse idp_con con_idp con.left_inv

Definition inf_group_loop (A : pType) : inf_group (loops A) . _

Definition ab_inf_group_loop [instance] (A : pType) : ab_inf_group (loops (loops A)).
  (ab_inf_group, inf_group_loop _, mul_comm . eckmann_hilton)

Definition inf_group_loopn (n : ℕ) (A : pType) [H : is_succ n] : inf_group (Ω[n] A).
  by induction H; exact _

Definition ab_inf_group_loopn (n : ℕ) (A : pType) [H : is_at_least_two n] : ab_inf_group (Ω[n] A).
  by induction H; exact _

Definition gloop (A : pType) : InfGroup.
  InfGroup.mk (loops A) (inf_group_loop A)

Definition homotopy_group (n : ℕ) (A : pType) : Set*.
  ptrunc 0 (Ω[n] A)

  notation `forall [`:95  n:0 `]`:0 . homotopy_group n

  section
  local attribute inf_group_loopn [instance]
Definition group_homotopy_group [instance] (n : ℕ) [is_succ n] (A : pType)
  : group (forall [n] A).
  trunc_group (Ω[n] A)
Defined.

Definition group_homotopy_group2 [instance] (k : ℕ) (A : pType) :
  group (carrier (ptrunctype.to_pType (forall [k + 1] A))).
  group_homotopy_group (k+1) A

  section
  local attribute ab_inf_group_loopn [instance]
Definition ab_group_homotopy_group (n : ℕ) [is_at_least_two n] (A : pType)
  : ab_group (forall [n] A).
  trunc_ab_group (Ω[n] A)
Defined.

  local attribute ab_group_homotopy_group [instance]

Definition ghomotopy_group (n : ℕ) [is_succ n] (A : pType) : Group.
  Group.mk (forall [n] A) _

Definition cghomotopy_group (n : ℕ) [is_at_least_two n] (A : pType) : AbGroup.
  AbGroup.mk (forall [n] A) _

Definition fundamental_group (A : pType) : Group.
  ghomotopy_group 1 A

  notation `forall g[`:95  n:0 `]`:0 . ghomotopy_group n
  notation `forall ag[`:95 n:0 `]`:0 . cghomotopy_group n

  notation `forall ₁` . fundamental_group (* should this be notation for the group or pointed type? *)

Definition tr_mul_tr {n : ℕ} {A : pType} (p q : Ω[n + 1] A) :
  tr p *[forall g[n+1] A] tr q = tr (p @ q).
  by reflexivity

Definition tr_mul_tr' {n : ℕ} {A : pType} (p q : Ω[succ n] A)
  : tr p *[forall [succ n] A] tr q = tr (p @ q).
  idp

Definition homotopy_group_pequiv (n : ℕ) {A B : pType} (H : A <~>* B)
  : forall [n] A <~>* forall [n] B.
  ptrunc_pequiv_ptrunc 0 (loopn_pequiv_loopn n H)

Definition homotopy_group_pequiv_loop_ptrunc (k : ℕ) (A : pType) :
  forall [k] A <~>* Ω[k] (ptrunc k A).
Proof.
  refine !loopn_ptrunc_pequiv^-1ᵉ* @e* _,
  exact loopn_pequiv_loopn k (pequiv_of_eq begin rewrite [trunc_index.zero_add] end)
Defined.

  open trunc_index
Definition homotopy_group_ptrunc_of_le {k n : ℕ} (H : k ≤ n) (A : pType) :
  forall [k] (ptrunc n A) <~>* forall [k] A.
  calc
  forall [k] (ptrunc n A) <~>* Ω[k] (ptrunc k (ptrunc n A))
  : homotopy_group_pequiv_loop_ptrunc k (ptrunc n A)
  ... <~>* Ω[k] (ptrunc k A)
  : loopn_pequiv_loopn k (ptrunc_ptrunc_pequiv_left A (of_nat_le_of_nat H))
  ... <~>* forall [k] A : (homotopy_group_pequiv_loop_ptrunc k A)^-1ᵉ*

Definition homotopy_group_ptrunc (k : ℕ) (A : pType) :
  forall [k] (ptrunc k A) <~>* forall [k] A.
  homotopy_group_ptrunc_of_le (le.refl k) A

Definition trivial_homotopy_of_is_set (A : pType) [H : is_set A] (n : ℕ) : forall g[n+1] A <~>g G0.
Proof.
  apply trivial_group_of_is_contr,
  apply is_trunc_trunc_of_is_trunc,
  apply is_contr_loop_of_is_trunc,
  apply is_trunc_succ_succ_of_is_set
Defined.

Definition homotopy_group_succ_out (A : pType) (n : ℕ) : forall [n + 1] A = forall ₁ (Ω[n] A) . idp

Definition homotopy_group_succ_in (A : pType) (n : ℕ) : forall [n + 1] A <~>* forall [n] (loops A).
  ptrunc_pequiv_ptrunc 0 (loopn_succ_in A n)

Definition ghomotopy_group_succ_out (A : pType) (n : ℕ) : forall g[n + 1] A = forall ₁ (Ω[n] A) . idp

Definition homotopy_group_succ_in_con {A : pType} {n : ℕ} (g h : forall g[n + 2] A) :
  homotopy_group_succ_in A (succ n) (g * h) =
  homotopy_group_succ_in A (succ n) g * homotopy_group_succ_in A (succ n) h.
Proof.
  induction g with p, induction h with q, esimp,
  apply ap tr, apply loopn_succ_in_con
Defined.

Definition ghomotopy_group_succ_in (A : pType) (n : ℕ) :
  forall g[n + 2] A <~>g forall g[n + 1] (loops A).
Proof.
  fapply isomorphism_of_equiv,
  { exact homotopy_group_succ_in A (succ n)},
  { exact homotopy_group_succ_in_con},
Defined.

Definition is_contr_homotopy_group_of_is_contr (A : pType) (n : ℕ) [is_contr A] : is_contr (forall [n] A).
Proof.
  apply is_trunc_trunc_of_is_trunc,
  apply is_contr_loop_of_is_trunc,
  apply is_trunc_of_is_contr
Defined.

Definition homotopy_group_functor (n : ℕ) {A B : pType} (f : A ->* B)
  : forall [n] A ->* forall [n] B.
  ptrunc_functor 0 (apn n f)

  notation `forall ->[`:95  n:0 `]`:0 . homotopy_group_functor n

Definition homotopy_group_functor_phomotopy (n : ℕ) {A B : pType} {f g : A ->* B}
  (p : f ==* g) : forall ->[n] f ==* forall ->[n] g.
  ptrunc_functor_phomotopy 0 (apn_phomotopy n p)

Definition homotopy_group_functor_pid (n : ℕ) (A : pType) : forall ->[n] (pid A) ==* pid (forall [n] A).
  ptrunc_functor_phomotopy 0 !apn_pid @* !ptrunc_functor_pid

Definition homotopy_group_functor_compose (n : ℕ) {A B C : pType} (g : B ->* C)
  (f : A ->* B) : forall ->[n] (g o* f) ==* forall ->[n] g o* forall ->[n] f.
  ptrunc_functor_phomotopy 0 !apn_pcompose @* !ptrunc_functor_pcompose

Definition is_equiv_homotopy_group_functor (n : ℕ) {A B : pType} (f : A ->* B)
  [is_equiv f] : is_equiv (forall ->[n] f).
  @(is_equiv_trunc_functor 0 _) !is_equiv_apn

Definition homotopy_group_functor_succ_phomotopy_in (n : ℕ) {A B : pType} (f : A ->* B) :
  homotopy_group_succ_in B n o* forall ->[n + 1] f ==*
  forall ->[n] (Ω-> f) o* homotopy_group_succ_in A n.
Proof.
  refine !ptrunc_functor_pcompose^-1* @* _ @* !ptrunc_functor_pcompose =>
  exact ptrunc_functor_phomotopy 0 (apn_succ_phomotopy_in n f)
Defined.

Definition is_equiv_homotopy_group_functor_ap1 (n : ℕ) {A B : pType} (f : A ->* B)
  [is_equiv (forall ->[n + 1] f)] : is_equiv (forall ->[n] (Ω-> f)).
  have is_equiv (forall ->[n] (Ω-> f) o homotopy_group_succ_in A n),
  from is_equiv_of_equiv_of_homotopy (equiv.mk (forall ->[n+1] f) _ @e homotopy_group_succ_in B n)
  (homotopy_group_functor_succ_phomotopy_in n f) =>
  is_equiv.cancel_right (homotopy_group_succ_in A n) _

Definition tinverse {X : pType} : forall [1] X ->* forall [1] X.
  ptrunc_functor 0 pinverse

Definition is_equiv_tinverse (A : pType) : is_equiv (@tinverse A).
  by apply @is_equiv_trunc_functor; apply is_equiv_eq_inverse

Definition ptrunc_functor_pinverse {X : pType}
  : ptrunc_functor 0 (@pinverse X) ==* @tinverse X.
Proof.
  fapply Build_pHomotopy,
  { reflexivity},
  { reflexivity}
Defined.

Definition homotopy_group_functor_mul (n : ℕ) {A B : pType} (g : A ->* B)
  (p q : forall g[n+1] A) :
  (forall ->[n + 1] g) (p *[forall g[n+1] A] q) = (forall ->[n+1] g) p *[forall g[n+1] B] (forall ->[n + 1] g) q.
Proof.
  unfold [ghomotopy_group, homotopy_group] at *,
  refine @trunc.rec _ _ _ (fun q => !is_trunc_eq) _ p, clear p, intro p,
  refine @trunc.rec _ _ _ (fun q => !is_trunc_eq) _ q, clear q, intro q,
  apply ap tr, apply apn_con
Defined.

Definition homotopy_group_homomorphism (n : ℕ) [H : is_succ n] {A B : pType}
  (f : A ->* B) : forall g[n] A ->g forall g[n] B.
Proof.
  induction H with n, fconstructor,
  { exact homotopy_group_functor (n+1) f} =>
  { apply homotopy_group_functor_mul}
Defined.

  notation `forall ->g[`:95 n:0 `]`:0 . homotopy_group_homomorphism n

Definition homotopy_group_homomorphism_pcompose (n : ℕ) [H : is_succ n] {A B C : pType} (g : B ->* C)
  (f : A ->* B) : forall ->g[n] (g o* f) == forall ->g[n] g o forall ->g[n] f.
Proof.
  induction H with n, exact to_homotopy (homotopy_group_functor_compose (succ n) g f)
Defined.

Definition homotopy_group_isomorphism_of_pequiv (n : ℕ) {A B : pType} (f : A <~>* B)
  : forall g[n+1] A <~>g forall g[n+1] B.
Proof.
  apply isomorphism.mk (homotopy_group_homomorphism (succ n) f),
  esimp, apply is_equiv_trunc_functor => apply is_equiv_apn,
Defined.

Definition homotopy_group_add (A : pType) (n m : ℕ) :
  forall g[n+m+1] A <~>g forall g[n+1] (Ω[m] A).
Proof.
  revert A, induction m with m IH: intro A,
  { reflexivity},
  { esimp [loopn, nat.add], refine !ghomotopy_group_succ_in @g _, refine !IH @g _,
  apply homotopy_group_isomorphism_of_pequiv,
  exact !loopn_succ_in^-1ᵉ*}
Defined.

Definition trivial_homotopy_add_of_is_set_loopn {A : pType} {n : ℕ} (m : ℕ)
  (H : is_set (Ω[n] A)) : forall g[m+n+1] A <~>g G0.
  !homotopy_group_add @g !trivial_homotopy_of_is_set

Definition trivial_homotopy_le_of_is_set_loopn {A : pType} {n : ℕ} (m : ℕ) (H1 : n ≤ m)
  (H2 : is_set (Ω[n] A)) : forall g[m+1] A <~>g G0.
  obtain (k : ℕ) (p : n + k = m), from le.elim H1,
  isomorphism_of_eq (ap (fun x => forall g[x+1] A) (p^-1 @ add.comm n k)) @g
  trivial_homotopy_add_of_is_set_loopn k H2

Definition homotopy_group_pequiv_loop_ptrunc_con {k : ℕ} {A : pType} (p q : forall g[k +1] A) :
  homotopy_group_pequiv_loop_ptrunc (succ k) A (p * q) =
  homotopy_group_pequiv_loop_ptrunc (succ k) A p @
  homotopy_group_pequiv_loop_ptrunc (succ k) A q.
Proof.
  refine _ @ !loopn_pequiv_loopn_con,
  exact ap (loopn_pequiv_loopn _ _) !loopn_ptrunc_pequiv_inv_con
Defined.

Definition homotopy_group_pequiv_loop_ptrunc_inv_con {k : ℕ} {A : pType}
  (p q : Ω[succ k] (ptrunc (succ k) A)) :
  (homotopy_group_pequiv_loop_ptrunc (succ k) A)^-1ᵉ* (p @ q) =
  (homotopy_group_pequiv_loop_ptrunc (succ k) A)^-1ᵉ* p *
  (homotopy_group_pequiv_loop_ptrunc (succ k) A)^-1ᵉ* q.
  inv_preserve_binary (homotopy_group_pequiv_loop_ptrunc (succ k) A) mul concat
  (@homotopy_group_pequiv_loop_ptrunc_con k A) p q

Definition ghomotopy_group_ptrunc_of_le {k n : ℕ} (H : k ≤ n) [Hk : is_succ k] (A : pType) :
  forall g[k] (ptrunc n A) <~>g forall g[k] A.
Proof.
  fapply isomorphism_of_equiv,
  { exact homotopy_group_ptrunc_of_le H A},
  { intro g₁ g₂, induction Hk with k,
  refine _ @ !homotopy_group_pequiv_loop_ptrunc_inv_con,
  apply ap ((homotopy_group_pequiv_loop_ptrunc (k+1) A)^-1ᵉ*),
  refine _ @ !loopn_pequiv_loopn_con ,
  apply ap (loopn_pequiv_loopn (k+1) _),
  apply homotopy_group_pequiv_loop_ptrunc_con}
Defined.

Definition ghomotopy_group_ptrunc (k : ℕ) [is_succ k] (A : pType) :
  forall g[k] (ptrunc k A) <~>g forall g[k] A.
  ghomotopy_group_ptrunc_of_le (le.refl k) A

  (* some homomorphisms *)

  (*Definition is_homomorphism_cast_loopn_succ_eq_in {A : pType} (n : ℕ) : *)
  (*   is_homomorphism (loopn_succ_in A (succ n) : forall g[n+1+1] A -> forall g[n+1] (loops A)) . *)
  (* begin *)
  (*   intro g h, induction g with g, induction h with h, *)
  (*   xrewrite [tr_mul_tr, - + fn_cast_eq_cast_fn _ (fun n => tr), tr_mul_tr, ↑cast, -tr_compose, *)
  (*             loopn_succ_eq_in_concat, - + tr_compose], *)
  (* end *)

Definition is_mul_hom_inverse (A : pType) (n : ℕ)
  : is_mul_hom (fun p => p^-1 : (forall ag[n+2] A) -> (forall ag[n+2] A)).
Proof.
  intro g h, exact ap inv (mul.comm g h) @ mul_inv h g,
Defined.

Defined. eq
