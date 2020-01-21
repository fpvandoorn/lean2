(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
*)

import ..move_to_lib types.fin types.trunc

open nat eq equiv sigma sigma.ops is_equiv is_trunc trunc prod fiber function is_conn

namespace seq_colim

Definition seq_diagram (A : ℕ -> Type) : Type . forall (n), A n -> A (succ n)

  structure Seq_diagram : Type.
  (carrier : ℕ -> Type)
  (struct : seq_diagram carrier)

Definition is_equiseq {A : ℕ -> Type} (f : seq_diagram A) : Type.
  forall (n : ℕ), is_equiv (@f n)

  structure Equi_seq : Type.
  (carrier : ℕ -> Type)
  (maps : seq_diagram carrier)
  (prop : is_equiseq maps)

  protected abbreviation Mk . Seq_diagram.mk
  attribute Seq_diagram.carrier [coercion]
  attribute Seq_diagram.struct [coercion]

  variables {A A' : ℕ -> Type} (f : seq_diagram A) (f' : seq_diagram A') {n m k : ℕ}
  include f

Definition lrep {n m : ℕ} (H : n ≤ m) : A n -> A m.
Proof.
  induction H with m H fs,
  { exact id },
  { exact @f m o fs }
Defined.

Definition lrep_irrel_pathover {n m m' : ℕ} (H₁ : n ≤ m) (H₂ : n ≤ m') (p : m = m') (a : A n) :
  lrep f H₁ a =[p] lrep f H₂ a.
  apo (fun m H => lrep f H a) !is_prop.elimo

Definition lrep_irrel {n m : ℕ} (H₁ H₂ : n ≤ m) (a : A n) : lrep f H₁ a = lrep f H₂ a.
  ap (fun H => lrep f H a) !is_prop.elim

Definition lrep_eq_transport {n m : ℕ} (H : n ≤ m) (p : n = m) (a : A n) : lrep f H a = transport A p a.
Proof. induction p, exact lrep_irrel f H (nat.le_refl n) a end

Definition lrep_irrel2 {n m : ℕ} (H₁ H₂ : n ≤ m) (a : A n) :
  lrep_irrel f (le.step H₁) (le.step H₂) a = ap (@f m) (lrep_irrel f H₁ H₂ a).
Proof.
  have H₁ = H₂, from !is_prop.elim, induction this,
  refine ap02 _ !is_prop_elim_self @ _ @ ap02 _(ap02 _ !is_prop_elim_self^-1),
  reflexivity
Defined.

Definition lrep_eq_lrep_irrel {n m m' : ℕ} (H₁ : n ≤ m) (H₂ : n ≤ m') (a₁ a₂ : A n) (p : m = m') :
  (lrep f H₁ a₁ = lrep f H₁ a₂) <~> (lrep f H₂ a₁ = lrep f H₂ a₂).
  equiv_apd011 (fun m H => lrep f H a₁ = lrep f H a₂) (is_prop.elimo p H₁ H₂)

Definition lrep_eq_lrep_irrel_natural {n m m' : ℕ} {H₁ : n ≤ m} (H₂ : n ≤ m') {a₁ a₂ : A n}
  (p : m = m') (q : lrep f H₁ a₁ = lrep f H₁ a₂) :
  lrep_eq_lrep_irrel f (le.step H₁) (le.step H₂) a₁ a₂ (ap succ p) (ap (@f m) q) =
  ap (@f m') (lrep_eq_lrep_irrel f H₁ H₂ a₁ a₂ p q).
Proof.
  esimp [lrep_eq_lrep_irrel],
  symmetry,
  refine fn_tro_eq_tro_fn2 _ (fun a₁ a₂ => ap (@f _)) q @ _,
  refine ap (fun x => x ▸o _) (@is_prop.elim _ _ _ _),
  apply is_trunc_pathover
Defined.

Definition is_equiv_lrep [Hf : is_equiseq f] {n m : ℕ} (H : n ≤ m) :
  is_equiv (lrep f H).
Proof.
  induction H with m H Hlrepf,
  { apply is_equiv_id },
  { exact is_equiv_compose (@f _) (lrep f H) _ _ },
Defined.

  local attribute is_equiv_lrep [instance]
Definition lrep_back [Hf : is_equiseq f] {n m : ℕ} (H : n ≤ m) : A m -> A n.
  (lrep f H)^-1ᶠ

  section generalized_lrep

  (* lreplace le_of_succ_le with this *)

Definition lrep_f {n m : ℕ} (H : succ n ≤ m) (a : A n) :
  lrep f H (f a) = lrep f (le_of_succ_le H) a.
Proof.
  induction H with m H p,
  { reflexivity },
  { exact ap (@f m) p }
Defined.

Definition lrep_lrep {n m k : ℕ} (H1 : n ≤ m) (H2 : m ≤ k) (a : A n) :
  lrep f H2 (lrep f H1 a) = lrep f (nat.le_trans H1 H2) a.
Proof.
  induction H2 with k H2 p,
  { reflexivity },
  { exact ap (@f k) p }
Defined.

Definition f_lrep {n m : ℕ} (H : n ≤ m) (a : A n) : f (lrep f H a) = lrep f (le.step H) a . idp

Definition rep (m : ℕ) (a : A n) : A (n + m).
  lrep f (le_add_right n m) a

Definition rep0 (m : ℕ) (a : A 0) : A m.
  lrep f (zero_le m) a

Definition rep_pathover_rep0 {n : ℕ} (a : A 0) : rep f n a =[nat.zero_add n] rep0 f n a.
  !lrep_irrel_pathover

Definition rep_f (k : ℕ) (a : A n) :
  pathover A (rep f k (f a)) (succ_add n k) (rep f (succ k) a).
Proof.
  induction k with k IH,
  { constructor },
  { unfold [succ_add], apply pathover_ap, exact apo f IH}
Defined.

Definition rep_rep (k l : ℕ) (a : A n) :
  pathover A (rep f k (rep f l a)) (nat.add_assoc n l k) (rep f (l + k) a).
Proof.
  induction k with k IH,
  { constructor},
  { apply pathover_ap, exact apo f IH}
Defined.

  variables {f f'}
Definition is_trunc_fun_lrep (k : ℕ₋₂) (H : n ≤ m) (H2 : forall , is_trunc_fun k (@f n)) :
  is_trunc_fun k (lrep f H).
Proof. induction H with m H IH, apply is_trunc_fun_id => exact is_trunc_fun_compose k (H2 m) IH end

Definition is_conn_fun_lrep (k : ℕ₋₂) (H : n ≤ m) (H2 : forall , is_conn_fun k (@f n)) :
  is_conn_fun k (lrep f H).
Proof. induction H with m H IH, apply is_conn_fun_id => exact is_conn_fun_compose k (H2 m) IH end

Definition lrep_natural (τ : forall (n), A n -> A' n) (p : forall (n) (a : A n), τ (f a) = f' (τ a))
  {n m : ℕ} (H : n ≤ m) (a : A n) : τ (lrep f H a) = lrep f' H (τ a).
Proof.
  induction H with m H IH, reflexivity, exact p (lrep f H a) @ ap (@f' m) IH
Defined.

Definition rep_natural (τ : forall (n), A n -> A' n) (p : forall (n) (a : A n), τ (f a) = f' (τ a))
  {n : ℕ} (k : ℕ) (a : A n) : τ (rep f k a) = rep f' k (τ a).
  lrep_natural τ p _ a

Definition rep0_natural (τ : forall (n), A n -> A' n) (p : forall (n) (a : A n), τ (f a) = f' (τ a))
  (k : ℕ) (a : A 0) : τ (rep0 f k a) = rep0 f' k (τ a).
  lrep_natural τ p _ a

  variables (f f')

Defined. generalized_lrep

  section shift

Definition shift_diag [unfold_full] : seq_diagram (fun n => A (succ n)).
  fun n a => f a

Definition kshift_diag [unfold_full] (k : ℕ) : seq_diagram (fun n => A (k + n)).
  fun n a => f a

Definition kshift_diag' [unfold_full] (k : ℕ) : seq_diagram (fun n => A (n + k)).
  fun n a => transport A (succ_add n k)^-1 (f a)

Definition lrep_kshift_diag {n m k : ℕ} (H : m ≤ k) (a : A (n + m)) :
  lrep (kshift_diag f n) H a = lrep f (nat.add_le_add_left2 H n) a.
  by induction H with k H p; reflexivity; exact ap (@f _) p

Defined. shift

  section constructions

  omit f

Definition constant_seq (X : Type) : seq_diagram (fun n => X).
  fun n x => x

Definition seq_diagram_arrow_left [unfold_full] (X : Type) : seq_diagram (fun n => X -> A n).
  fun n g x => f (g x)

Definition seq_diagram_prod [unfold_full] : seq_diagram (fun n => A n \* A' n).
  fun n => prod_functor (@f n) (@f' n)

  open fin
Definition seq_diagram_fin [unfold_full] : seq_diagram fin.
  lift_succ

Definition id0_seq [unfold_full] (a₁ a₂ : A 0) : ℕ -> Type.
  fun k => rep0 f k a₁ = rep0 f k a₂

Definition id0_seq_diagram [unfold_full] (a₁ a₂ : A 0) : seq_diagram (id0_seq f a₁ a₂).
  fun (k : ℕ) (p : rep0 f k a₁ = rep0 f k a₂) => ap (@f k) p

Definition id_seq [unfold_full] (n : ℕ) (a₁ a₂ : A n) : ℕ -> Type.
  fun k => rep f k a₁ = rep f k a₂

Definition id_seq_diagram [unfold_full] (n : ℕ) (a₁ a₂ : A n) : seq_diagram (id_seq f n a₁ a₂).
  fun (k : ℕ) (p : rep f k a₁ = rep f k a₂) => ap (@f (n + k)) p

Definition trunc_diagram [unfold_full] (k : ℕ₋₂) (f : seq_diagram A) :
  seq_diagram (fun n => trunc k (A n)).
  fun n => trunc_functor k (@f n)

Defined. constructions

  section over

  variable {A}
  variable (P : forall (n), A n -> Type)

Definition seq_diagram_over : Type . forall (n) {a : A n}, P a -> P (f a)

Definition weakened_sequence [unfold_full] : seq_diagram_over f (fun n a => A' n).
  fun n a a' => f' a'

Definition id0_seq_diagram_over [unfold_full] (a₀ : A 0) :
  seq_diagram_over f (fun n a => rep0 f n a₀ = a).
  fun n a p => ap (@f n) p

  variable (g : seq_diagram_over f P)
  variables {f P}

Definition seq_diagram_of_over [unfold_full] {n : ℕ} (a : A n) :
  seq_diagram (fun k => P (rep f k a)).
  fun k p => g p

Definition seq_diagram_sigma : seq_diagram (fun n => Σ(x : A n), P x).
  fun n v => ⟨f v.1, g v.2⟩

  variables (f P)

Definition rep_f_equiv (a : A n) (k : ℕ) :
  P (lrep f (le_add_right (succ n) k) (f a)) <~> P (lrep f (le_add_right n (succ k)) a).
  equiv_apd011 P (rep_f f k a)

Definition rep_rep_equiv (a : A n) (k l : ℕ) :
  P (rep f (l + k) a) <~> P (rep f k (rep f l a)).
  (equiv_apd011 P (rep_rep f k l a))^-1ᵉ

Defined. over

  omit f
Definition seq_diagram_pi {X : Type} {A : X -> ℕ -> Type} (g : forall (x n), A x n -> A x (succ n)) :
  seq_diagram (fun n => forall x, A x n).
  fun n f x => g (f x)

  variables {f f'}
Definition seq_diagram_over_fiber (g : forall (n), A' n -> A n)
  (p : forall (n) (a : A' n), g (f' a) = f (g a)) : seq_diagram_over f (fun n => fiber (@g n)).
  fun k a => fiber_functor (@f' k) (@f k) (@p k) idp

Definition seq_diagram_fiber (g : forall (n), A' n -> A n) (p : forall (n) (a : A' n), g (f' a) = f (g a))
  {n : ℕ} (a : A n) : seq_diagram (fun k => fiber (@g (n + k)) (rep f k a)).
  seq_diagram_of_over (seq_diagram_over_fiber g p) a

Definition seq_diagram_fiber0 (g : forall (n), A' n -> A n) (p : forall (n) (a : A' n), g (f' a) = f (g a))
  (a : A 0) : seq_diagram (fun k => fiber (@g k) (rep0 f k a)).
  fun k => fiber_functor (@f' k) (@f k) (@p k) idp


Defined. seq_colim
