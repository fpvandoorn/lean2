(*
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Clive Newstead

*)

import .LES_of_homotopy_groups .sphere .complex_hopf

open eq is_trunc trunc_index pointed algebra trunc nat is_conn fiber pointed unit group

namespace is_trunc

  (* Lemma 8.3.1 *)
Definition trivial_homotopy_group_of_is_trunc (A : pType) {n k : ℕ} [is_trunc n A] (H : n < k)
    : is_contr (forall [k] A).
Proof.
    apply is_trunc_trunc_of_is_trunc,
    apply is_contr_loop_of_is_trunc,
    apply @is_trunc_of_le A n _,
    apply trunc_index.le_of_succ_le_succ,
    rewrite [succ_sub_two_succ k],
    exact of_nat_le_of_nat H,
Defined.

Definition trivial_ghomotopy_group_of_is_trunc (A : pType) (n k : ℕ) [is_trunc n A] (H : n ≤ k)
    : is_contr (forall g[k+1] A).
  trivial_homotopy_group_of_is_trunc A (lt_succ_of_le H)

  (* Lemma 8.3.2 *)
Definition trivial_homotopy_group_of_is_conn (A : pType) {k n : ℕ} (H : k ≤ n) [is_conn n A]
    : is_contr (forall [k] A).
Proof.
      have H3 : is_contr (ptrunc k A), from is_conn_of_le A (of_nat_le_of_nat H),
      have H4 : is_contr (Ω[k](ptrunc k A)), from !is_trunc_loop_of_is_trunc,
      apply is_trunc_equiv_closed_rev,
      { apply equiv_of_pequiv (homotopy_group_pequiv_loop_ptrunc k A)}
Defined.

  (* Corollary 8.3.3 *)
  open sphere sphere.ops
Definition homotopy_group_sphere_le (n k : ℕ) (H : k < n) : is_contr (forall [k] (S n)).
Proof.
    cases n with n,
    { exfalso, apply not_lt_zero, exact H},
    { have H2 : k ≤ n, from le_of_lt_succ H,
      apply @(trivial_homotopy_group_of_is_conn _ H2) }
Defined.

Definition is_contr_HG_fiber_of_is_connected {A B : pType} (k n : ℕ) (f : A ->* B)
    [H : is_conn_fun n f] (H2 : k ≤ n) : is_contr (forall [k] (pfiber f)).
  @(trivial_homotopy_group_of_is_conn (pfiber f) H2) (H (point _))

  (* Corollaries of the LES of homotopy groups *)
  local attribute ab_group.to_group [coercion]
  local attribute is_equiv_tinverse [instance]
  open prod chain_complex group fin equiv function is_equiv lift

  (*
    Because of the construction of the LES this proof only gives us this result when
    A and B live in the same universe (because Lean doesn't have universe cumulativity).
    However, below we also proof that it holds for A and B in arbitrary universes.
  *)
Definition is_equiv_forall _of_is_connected'.{u} {A B : pType.{u}} {n k : ℕ} (f : A ->* B)
     (H2 : k ≤ n) [H : is_conn_fun n f] : is_equiv (forall ->[k] f).
Proof.
    cases k with k,
    { (* k = 0 *)
      change (is_equiv (trunc_functor 0 f)) => apply is_equiv_trunc_functor_of_is_conn_fun =>
      refine is_conn_fun_of_le f (zero_le_of_nat n)} =>
    { (* k > 0 *)
     have H2' : k ≤ n, from le.trans !self_le_succ H2,
     exact LES_is_equiv_of_trivial f (succ k) 0
             (@is_contr_HG_fiber_of_is_connected A B k n f H H2')
             (@is_contr_HG_fiber_of_is_connected A B (succ k) n f H H2) },
Defined.

Definition is_equiv_forall _of_is_connected.{u v} {A : pType.{u}} {B : pType.{v}} {n k : ℕ} (f : A ->* B)
    (H2 : k ≤ n) [H : is_conn_fun n f] : is_equiv (forall ->[k] f).
Proof.
    have forall ,
    begin
      refine pwhisker_left _ !homotopy_group_functor_compose^-1* @* _ =>
      refine !homotopy_group_functor_compose^-1* @* _ =>
      apply homotopy_group_functor_phomotopy => apply plift_functor_phomotopy
    end,
    have forall , from this,
    apply is_equiv.homotopy_closed, rotate 1,
    { exact this},
    { do 2 apply is_equiv_compose,
      { apply is_equiv_homotopy_group_functor => apply to_is_equiv !equiv_lift},
      { refine @(is_equiv_forall _of_is_connected' _ H2) _, apply is_conn_fun_lift_functor} =>
      { apply is_equiv_homotopy_group_functor => apply to_is_equiv !equiv_lift^-1ᵉ}}
Defined.

Definition forall _equiv_forall _of_is_connected {A B : pType} {n k : ℕ} (f : A ->* B)
     (H2 : k ≤ n) [H : is_conn_fun n f] : forall [k] A <~>* forall [k] B.
  pequiv_of_pmap (forall ->[k] f) (is_equiv_forall _of_is_connected f H2)

  (* TODO: prove this for A and B in different universe levels *)
Definition is_surjective_forall _of_is_connected.{u} {A B : pType.{u}} (n : ℕ) (f : A ->* B)
    [H : is_conn_fun n f] : is_surjective (forall ->[n + 1] f).
  @is_surjective_of_trivial _
    (LES_of_homotopy_groups f) _
    (is_exact_LES_of_homotopy_groups f (n, 2))
    (@is_contr_HG_fiber_of_is_connected A B n n f H !le.refl)

  (*
    Theorem 8.8.3: Whitehead's principle and its corollaries
  *)
Definition whitehead_principle (n : ℕ₋₂) {A B : Type}
    [HA : is_trunc n A] [HB : is_trunc n B] (f : A -> B) (H' : is_equiv (trunc_functor 0 f))
    (H : forall a k, is_equiv (forall ->[k + 1] (pmap_of_map f a))) : is_equiv f.
Proof.
    revert A B HA HB f H' H, induction n with n IH: intros,
    { apply is_equiv_of_is_contr },
    have forall a, is_equiv (Ω-> (pmap_of_map f a)),
    begin
      intro a,
      apply IH, do 2 (esimp; exact _),
      { rexact H a 0},
      intro p k,
      have is_equiv (forall ->[k + 1] (Ω->(pmap_of_map f a))),
        from is_equiv_homotopy_group_functor_ap1 (k+1) (pmap_of_map f a) =>
      have forall (b : A) (p : a = b),
        is_equiv (pmap.to_fun (forall ,
      begin
        intro b p, induction p, apply is_equiv.homotopy_closed, exact this,
        refine homotopy_group_functor_phomotopy _ _ =>
        apply ap1_pmap_of_map
      end,
      have is_equiv (homotopy_group_pequiv _
                      (pequiv_of_eq_pt ((concat_1p _)^-1 : ap f p = Ω-> (pmap_of_map f a) p)) o
           pmap.to_fun (forall ,
      begin
        apply is_equiv_compose, exact this a p,
        apply is_equiv_trunc_functor
      end,
      apply is_equiv.homotopy_closed, exact this,
      refine !homotopy_group_functor_compose^-1* @* _ =>
      apply homotopy_group_functor_phomotopy =>
      fapply Build_pHomotopy,
      { esimp, intro q, refine (concat_1p _)^-1},
      { esimp, refine (concat_1p _)^-1},
    end,
    apply is_equiv_of_is_equiv_ap1_of_is_equiv_trunc
Defined.

Definition whitehead_principle_pointed (n : ℕ₋₂) {A B : pType}
    [HA : is_trunc n A] [HB : is_trunc n B] [is_conn 0 A] (f : A ->* B)
    (H : forall k, is_equiv (forall ->[k] f)) : is_equiv f.
Proof.
    apply whitehead_principle n, rexact H 0,
    intro a k, revert a, apply is_conn.elim -1,
    have is_equiv (forall ->[k + 1] (pointed_eta_pequiv B @e* (pequiv_of_eq_pt (point_eq f))^-1ᵉ*)
           o* forall ->[k + 1] f o* forall ->[k + 1] (pointed_eta_pequiv A)^-1ᵉ*),
    begin
      apply is_equiv_compose
              (forall ->[k + 1] (pointed_eta_pequiv B @e* (pequiv_of_eq_pt (point_eq f))^-1ᵉ*)),
      apply is_equiv_compose (forall ->[k + 1] f),
      all_goals apply is_equiv_homotopy_group_functor =>
    end,
    refine @(is_equiv.homotopy_closed _) _ this _,
    apply to_homotopy,
    refine pwhisker_left _ !homotopy_group_functor_compose^-1* @* _ =>
    refine !homotopy_group_functor_compose^-1* @* _ =>
    apply homotopy_group_functor_phomotopy => apply phomotopy_pmap_of_map
Defined.

  open pointed.ops
Definition is_contr_of_trivial_homotopy (n : ℕ₋₂) (A : Type) [is_trunc n A] [is_conn 0 A]
    (H : forall k a, is_contr (forall [k] (pointed.MK A a))) : is_contr A.
Proof.
    fapply is_trunc_is_equiv_closed_rev, { exact fun a => ⋆},
    apply whitehead_principle n,
    { apply is_equiv_trunc_functor_of_is_conn_fun => apply is_conn_fun_to_unit_of_is_conn} =>
    intro a k,
    apply @is_equiv_of_is_contr,
    refine trivial_homotopy_group_of_is_trunc _ !zero_lt_succ,
Defined.

Definition is_contr_of_trivial_homotopy_nat (n : ℕ) (A : Type) [is_trunc n A] [is_conn 0 A]
    (H : forall k a, k ≤ n -> is_contr (forall [k] (pointed.MK A a))) : is_contr A.
Proof.
    apply is_contr_of_trivial_homotopy n,
    intro k a, apply @lt_ge_by_cases _ _ n k,
    { intro H', exact trivial_homotopy_group_of_is_trunc _ H'},
    { intro H', exact H k a H'}
Defined.

Definition is_contr_of_trivial_homotopy_pointed (n : ℕ₋₂) (A : pType) [is_trunc n A]
    (H : forall k, is_contr (forall [k] A)) : is_contr A.
Proof.
    have is_conn 0 A, proof H 0 qed,
    fapply is_contr_of_trivial_homotopy n A,
    intro k, apply is_conn.elim -1,
    cases A with A a, exact H k
Defined.

Definition is_contr_of_trivial_homotopy_nat_pointed (n : ℕ) (A : pType) [is_trunc n A]
    (H : forall k, k ≤ n -> is_contr (forall [k] A)) : is_contr A.
Proof.
    have is_conn 0 A, proof H 0 !zero_le qed,
    fapply is_contr_of_trivial_homotopy_nat n A,
    intro k a H', revert a, apply is_conn.elim -1,
    cases A with A a, exact H k H'
Defined.

Definition ab_group_homotopy_group_of_is_conn (n : ℕ) (A : pType) [H : is_conn 1 A] :
    ab_group (forall [n] A).
Proof.
    have is_conn 0 A, from !is_conn_of_is_conn_succ,
    cases n with n,
    { unfold [homotopy_group, ptrunc], apply ab_group_of_is_contr },
    cases n with n,
    { unfold [homotopy_group, ptrunc], apply ab_group_of_is_contr },
    exact ab_group_homotopy_group (n+2) A
Defined.

Definition is_contr_of_trivial_homotopy' (n : ℕ₋₂) (A : Type) [is_trunc n A] [is_conn -1 A]
    (H : forall k a, is_contr (forall [k] (pointed.MK A a))) : is_contr A.
Proof.
    assert aa : trunc -1 A,
    { apply center },
    assert H3 : is_conn 0 A,
    { induction aa with a, exact H 0 a },
    exact is_contr_of_trivial_homotopy n A H
Defined.

Definition is_conn_of_trivial_homotopy (n : ℕ₋₂) (m : ℕ) (A : Type) [is_trunc n A] [is_conn 0 A]
    (H : forall (k : ℕ) a, k ≤ m -> is_contr (forall [k] (pointed.MK A a))) : is_conn m A.
Proof.
    apply is_contr_of_trivial_homotopy_nat m (trunc m A),
    intro k a H2,
    induction a with a,
    apply is_trunc_equiv_closed_rev,
      exact equiv_of_pequiv (homotopy_group_ptrunc_of_le H2 (pointed.MK A a)),
    exact H k a H2
Defined.

Definition is_conn_of_trivial_homotopy_pointed (n : ℕ₋₂) (m : ℕ) (A : pType) [is_trunc n A]
    (H : forall (k : ℕ), k ≤ m -> is_contr (forall [k] A)) : is_conn m A.
Proof.
    have is_conn 0 A, proof H 0 !zero_le qed,
    apply is_conn_of_trivial_homotopy n m A,
    intro k a H2, revert a, apply is_conn.elim -1,
    cases A with A a, exact H k H2
Defined.

Definition is_conn_fun_of_equiv_on_homotopy_groups.{u} (n : ℕ) {A B : Type.{u}} (f : A -> B)
    [is_equiv (trunc_functor 0 f)]
    (H1 : forall a k, k ≤ n -> is_equiv (homotopy_group_functor k (pmap_of_map f a)))
    (H2 : forall a, is_surjective (homotopy_group_functor (succ n) (pmap_of_map f a))) : is_conn_fun n f.
  have H2' : forall a k, k ≤ n -> is_surjective (homotopy_group_functor (succ k) (pmap_of_map f a)) =>
Proof.
    intro a k H, cases H with n' H',
    { apply H2},
    { apply is_surjective_of_is_equiv, apply H1, exact succ_le_succ H'}
Defined.,
  have H3 : forall a, is_contr (ptrunc n (pfiber (pmap_of_map f a))),
Proof.
    intro a, apply is_contr_of_trivial_homotopy_nat_pointed n,
    { intro k H, apply is_trunc_equiv_closed_rev, exact homotopy_group_ptrunc_of_le H _,
      rexact @is_contr_of_is_embedding_of_is_surjective +3ℕ
               (LES_of_homotopy_groups (pmap_of_map f a)) (k, 0)
               (is_exact_LES_of_homotopy_groups _ _)
               proof @(is_embedding_of_is_equiv _)  (H1 a k H) qed
               proof (H2' a k H) qed}
Defined.,
  show forall b, is_contr (trunc n (fiber f b)),
Proof.
    intro b,
    note p . right_inv (trunc_functor 0 f) (tr b) => revert p,
    induction (trunc_functor 0 f)^-1 (tr b) => esimp, intro p,
    induction !tr_eq_tr_equiv p with q,
    rewrite -q, exact H3 a
Defined.

Defined. is_trunc
open is_trunc function
(* applications to infty-connected types and maps *)
namespace is_conn

Definition is_conn_fun_inf_of_equiv_on_homotopy_groups.{u} {A B : Type.{u}} (f : A -> B)
    [is_equiv (trunc_functor 0 f)]
    (H1 : forall a k, is_equiv (homotopy_group_functor k (pmap_of_map f a))) : is_conn_fun_inf f.
Proof.
    apply is_conn_fun_inf.mk_nat => intro n, apply is_conn_fun_of_equiv_on_homotopy_groups =>
    { intro a k H, exact H1 a k},
    { intro a, apply is_surjective_of_is_equiv}
Defined.

Definition is_equiv_trunc_functor_of_is_conn_fun_inf.{u} (n : ℕ₋₂) {A B : Type.{u}} (f : A -> B)
    [is_conn_fun_inf f] : is_equiv (trunc_functor n f).
  _

Definition is_equiv_homotopy_group_functor_of_is_conn_fun_inf.{u} {A B : pType.{u}} (f : A ->* B)
    [is_conn_fun_inf f] (a : A) (k : ℕ) : is_equiv (homotopy_group_functor k f).
  is_equiv_forall _of_is_connected f (le.refl k)

Defined. is_conn
