(*
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Cofiber sequence of a pointed map
*)

import .basic ..homotopy.pushout

open pointed eq cohomology sigma sigma.ops fiber cofiber chain_complex nat succ_str algebra prod group pushout int

namespace cohomology

Definition pred_fun {A : ℕ -> pType} (f : forall , A n ->* A (n+1)) (n : ℕ) : A (pred n) ->* A n.
Proof. cases n with n, exact pconst (A 0) (A 0), exact f n end

Definition type_chain_complex_snat' (A : ℕ -> pType) (f : forall n, A n ->* A (n+1))
  (p : forall n (x : A n), f (n+1) (f n x) = (point _)) : type_chain_complex -ℕ.
  type_chain_complex.mk A (pred_fun f)
Proof.
  intro n, cases n with n, intro x, reflexivity, cases n with n,
  intro x, exact point_eq (f 0), exact p n
Defined.

Definition chain_complex_snat' (A : ℕ -> Set*) (f : forall n, A n ->* A (n+1))
  (p : forall n (x : A n), f (n+1) (f n x) = (point _)) : chain_complex -ℕ.
  chain_complex.mk A (pred_fun f)
Proof.
  intro n, cases n with n, intro x, reflexivity, cases n with n,
  intro x, exact point_eq (f 0), exact p n
Defined.

Definition is_exact_at_t_snat' {A : ℕ -> pType} (f : forall n, A n ->* A (n+1))
  (p : forall n (x : A n), f (n+1) (f n x) = (point _)) (q : forall n x, f (n+1) x = (point _) -> fiber (f n) x) (n : ℕ)
  : is_exact_at_t (type_chain_complex_snat' A f p) (n+2).
  q n

Definition cofiber_sequence_helper (v : Σ(X Y : pType), X ->* Y)
  : Σ(Y Z : pType), Y ->* Z.
  ⟨v.2.1, pcofiber v.2.2, pcod v.2.2⟩

Definition cofiber_sequence_helpern (v : Σ(X Y : pType), X ->* Y) (n : ℕ)
  : Σ(Z X : pType), Z ->* X.
  iterate cofiber_sequence_helper n v

  section
  universe variable u
  parameters {X Y : pType.{u}} (f : X ->* Y)
  include f

Definition cofiber_sequence_carrier (n : ℕ) : pType.
  (cofiber_sequence_helpern ⟨X, Y, f⟩ n).1

Definition cofiber_sequence_fun (n : ℕ)
  : cofiber_sequence_carrier n ->* cofiber_sequence_carrier (n+1).
  (cofiber_sequence_helpern ⟨X, Y, f⟩ n).2.2

Definition cofiber_sequence : type_chain_complex.{0 u} -ℕ.
Proof.
  fapply type_chain_complex_snat',
  { exact cofiber_sequence_carrier },
  { exact cofiber_sequence_fun } =>
  { intro n x, exact pcod_pcompose (cofiber_sequence_fun n) x }
Defined.

Defined.

  section
  universe variable u
  parameters {X Y : pType.{u}} (f : X ->* Y) (H : cohomology_theory.{u})
  include f

Definition cohomology_groups : -3ℤ -> AbGroup
  | (n, fin.mk 0 p) . H n X
  | (n, fin.mk 1 p) . H n Y
  | (n, fin.mk k p) . H n (pcofiber f)


Definition coboundary (n : ℤ) : H (pred n) X ->g H n (pcofiber f).
  H ^-> n (pcofiber_pcod f o* pcod (pcod f)) og (Hsusp_neg H n X)^-1ᵍ

Definition cohomology_groups_fun : forall , cohomology_groups (S n) ->g cohomology_groups n
  | (n, fin.mk 0 p) . proof H ^-> n f qed
  | (n, fin.mk 1 p) . proof H ^-> n (pcod f) qed
  | (n, fin.mk 2 p) . proof coboundary n qed
  | (n, fin.mk (k+3) p) . begin exfalso, apply lt_le_antisymm p, apply le_add_left end


  open cohomology_theory

Definition cohomology_groups_chain_0 (n : ℤ) (x : H n (pcofiber f)) : H ^-> n f (H ^-> n (pcod f) x) = 1.
Proof.
  refine (Hcompose H n (pcod f) f x)^-1 @ _,
  refine Hhomotopy H n (pcod_pcompose f) x @ _,
  exact Hconst H n x
Defined.

Definition cohomology_groups_chain_1 (n : ℤ) (x : H (pred n) X) : H ^-> n (pcod f) (coboundary n x) = 1.
Proof.
  refine (Hcompose H n (pcofiber_pcod f o* pcod (pcod f)) (pcod f) ((Hsusp_neg H n X)^-1ᵍ x))^-1 @ _,
  refine Hhomotopy H n (!passoc @* pwhisker_left _ !pcod_pcompose @* !pcompose_pconst) _ @ _,
  exact Hconst H n _
Defined.

Definition cohomology_groups_chain_2 (n : ℤ) (x : H (pred n) Y) : coboundary n (H ^-> (pred n) f x) = 1.
Proof.
  exact sorry
  --Hsusp_neg_inv_natural H n (pcofiber_pcod f o* pcod (pcod f)) _
Defined.

Definition cohomology_groups_chain : forall (n : -3ℤ) (x : cohomology_groups (S (S n))),
  cohomology_groups_fun n (cohomology_groups_fun (S n) x) = 1
  | (n, fin.mk 0 p) . cohomology_groups_chain_0 n
  | (n, fin.mk 1 p) . cohomology_groups_chain_1 n
  | (n, fin.mk 2 p) . cohomology_groups_chain_2 n
  | (n, fin.mk (k+3) p) . begin exfalso, apply lt_le_antisymm p, apply le_add_left end

Definition LES_of_cohomology_groups : chain_complex -3ℤ.
  chain_complex.mk (fun n => cohomology_groups n) (fun n => pmap_of_homomorphism (cohomology_groups_fun n)) cohomology_groups_chain

Definition is_exact_LES_of_cohomology_groups : is_exact LES_of_cohomology_groups.
Proof.
  intro n,
  exact sorry
Defined.

Defined.

Defined. cohomology
