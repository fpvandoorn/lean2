(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
*)
prelude
import init.tactic init.num init.types init.path
open eq eq.ops decidable
open algebra sum
set_option class.force_new true

notation `ℕ` . nat

namespace nat
  protectedDefinition rec_on [recursor] [unfold 2]
                       {C : ℕ -> Type} (n : ℕ) (H₁ : C 0) (H₂ : forall (a : ℕ), C a -> C (succ a)) : C n.
  nat.rec H₁ H₂ n

  protectedDefinition cases {M : ℕ -> Type} (mz : M zero)
    (ms : forall n, M (succ n)) : forall n, M n.
  nat.rec mz (fun n dummy => ms n)

  protectedDefinition cases_on [recursor] [unfold 2]
                       {C : ℕ -> Type} (n : ℕ) (H₁ : C 0) (H₂ : forall (a : ℕ), C (succ a)) : C n.
  nat.rec H₁ (fun a ih => H₂ a) n

  protectedDefinition no_confusion_type.{u} (P : Type.{u}) (v₁ v₂ : ℕ) : Type.{u}.
  nat.rec
    (nat.rec
       (P -> lift P)
       (fun a₂ ih => lift P)
       v₂)
    (fun a₁ ih => nat.rec
       (lift P)
       (fun a₂ ih => (a₁ = a₂ -> P) -> lift P)
       v₂)
    v₁

  protectedDefinition no_confusion [unfold 4]
                       {P : Type} {v₁ v₂ : ℕ} (H : v₁ = v₂) : nat.no_confusion_type P v₁ v₂.
  eq.rec (fun H₁ : v₁ = v₁ => nat.rec (fun h => lift.up h) (fun a ih h => lift.up (h (eq.refl a))) v₁) H H

  (* basicDefinitions on natural numbers *)
  inductive le (a : ℕ) : ℕ -> Type.
  | nat_refl : le a a    (* use nat_refl to avoid overloading le.refl *)
  | step : forall {b}, le a b -> le a (succ b)

Definition nat_has_le [instance] [priority nat.prio]: has_le nat . has_le.mk nat.le

  protectedDefinition le_refl [refl] : forall a : nat, a ≤ a.
  le.nat_refl

  protectedDefinition lt (n m : ℕ) . succ n ≤ m
Definition nat_has_lt [instance] [priority nat.prio] : has_lt nat . has_lt.mk nat.lt

Definition pred (a : nat) : nat.
  nat.cases_on a zero (fun a₁ => a₁)

  (* add is defined in init.reserved_notation *)

  protectedDefinition sub (a b : nat) : nat.
  nat.rec_on b a (fun b₁ => pred)

  protectedDefinition mul (a b : nat) : nat.
  nat.rec_on b zero (fun b₁ r => r + a)

Definition nat_has_sub [instance] [priority nat.prio] : has_sub nat.
  has_sub.mk nat.sub

Definition nat_has_mul [instance] [priority nat.prio] : has_mul nat.
  has_mul.mk nat.mul

  (* properties of ℕ *)

  protectedDefinition is_inhabited [instance] : inhabited nat.
  inhabited.mk zero

  protectedDefinition has_decidable_eq [instance] [priority nat.prio] : forall x y : nat, decidable (x = y)
  | has_decidable_eq zero     zero     . inl rfl
  | has_decidable_eq (succ x) zero     . inr (by contradiction)
  | has_decidable_eq zero     (succ y) . inr (by contradiction)
  | has_decidable_eq (succ x) (succ y).
      match has_decidable_eq x y with
      | inl xeqy . inl (by rewrite xeqy)
      | inr xney . inr (fun h : succ x = succ y => by injection h with xeqy; exact absurd xeqy xney)
      end

  (* properties of inequality *)

  protectedDefinition le_of_eq {n m : ℕ} (p : n = m) : n ≤ m . p # !nat.le_refl

Definition le_succ (n : ℕ) : n ≤ succ n . le.step !nat.le_refl

Definition pred_le (n : ℕ) : pred n ≤ n . by cases n;repeat constructor

Definition le_succ_iff_unit [simp] (n : ℕ) : n ≤ succ n ↔ unit.
  iff_unit_intro (le_succ n)

Definition pred_le_iff_unit [simp] (n : ℕ) : pred n ≤ n ↔ unit.
  iff_unit_intro (pred_le n)

  protectedDefinition le_trans {n m k : ℕ} (H1 : n ≤ m) : m ≤ k -> n ≤ k.
  le.rec H1 (fun p H2 => le.step)

Definition le_succ_of_le {n m : ℕ} (H : n ≤ m) : n ≤ succ m . nat.le_trans H !le_succ

Definition le_of_succ_le {n m : ℕ} (H : succ n ≤ m) : n ≤ m . nat.le_trans !le_succ H

  protectedDefinition le_of_lt {n m : ℕ} (H : n < m) : n ≤ m . le_of_succ_le H

Definition succ_le_succ {n m : ℕ} : n ≤ m -> succ n ≤ succ m.
  le.rec !nat.le_refl (fun a b => le.step)

Definition pred_le_pred {n m : ℕ} : n ≤ m -> pred n ≤ pred m.
  le.rec !nat.le_refl (nat.rec (fun a b => b) (fun a b c => le.step))

Definition le_of_succ_le_succ {n m : ℕ} : succ n ≤ succ m -> n ≤ m.
  pred_le_pred

Definition le_succ_of_pred_le {n m : ℕ} : pred n ≤ m -> n ≤ succ m.
  nat.cases_on n le.step (fun a => succ_le_succ)

Definition not_succ_le_zero (n : ℕ) : ¬succ n ≤ 0.
  by intro H; cases H

Definition succ_le_zero_iff_empty (n : ℕ) : succ n ≤ 0 ↔ empty.
  iff_empty_intro !not_succ_le_zero

Definition not_succ_le_self : forall {n : ℕ}, ¬succ n ≤ n.
  nat.rec !not_succ_le_zero (fun a b c => b (le_of_succ_le_succ c))

Definition succ_le_self_iff_empty [simp] (n : ℕ) : succ n ≤ n ↔ empty.
  iff_empty_intro not_succ_le_self

Definition zero_le : forall (n : ℕ), 0 ≤ n.
  nat.rec !nat.le_refl (fun a => le.step)

Definition zero_le_iff_unit [simp] (n : ℕ) : 0 ≤ n ↔ unit.
  iff_unit_intro !zero_le

Definition lt.step {n m : ℕ} : n < m -> n < succ m . le.step

Definition zero_lt_succ (n : ℕ) : 0 < succ n.
  succ_le_succ !zero_le

Definition zero_lt_succ_iff_unit [simp] (n : ℕ) : 0 < succ n ↔ unit.
  iff_unit_intro (zero_lt_succ n)

  protectedDefinition lt_trans {n m k : ℕ} (H1 : n < m) : m < k -> n < k.
  nat.le_trans (le.step H1)

  protectedDefinition lt_of_le_of_lt {n m k : ℕ} (H1 : n ≤ m) : m < k -> n < k.
  nat.le_trans (succ_le_succ H1)

  protectedDefinition lt_of_lt_of_le {n m k : ℕ} : n < m -> m ≤ k -> n < k . nat.le_trans

  protectedDefinition lt_irrefl (n : ℕ) : ¬n < n . not_succ_le_self

Definition lt_self_iff_empty (n : ℕ) : n < n ↔ empty.
  iff_empty_intro (fun H => absurd H (nat.lt_irrefl n))

Definition self_lt_succ (n : ℕ) : n < succ n . !nat.le_refl

Definition self_lt_succ_iff_unit [simp] (n : ℕ) : n < succ n ↔ unit.
  iff_unit_intro (self_lt_succ n)

Definition lt.base (n : ℕ) : n < succ n . !nat.le_refl

Definition le_lt_antisymm {n m : ℕ} (H1 : n ≤ m) (H2 : m < n) : empty.
  !nat.lt_irrefl (nat.lt_of_le_of_lt H1 H2)

  protectedDefinition le_antisymm {n m : ℕ} (H1 : n ≤ m) : m ≤ n -> n = m.
  le.cases_on H1 (fun a => rfl) (fun a b c => absurd (nat.lt_of_le_of_lt b c) !nat.lt_irrefl)

Definition lt_le_antisymm {n m : ℕ} (H1 : n < m) (H2 : m ≤ n) : empty.
  le_lt_antisymm H2 H1

  protectedDefinition nat.lt_asymm {n m : ℕ} (H1 : n < m) : ¬ m < n.
  le_lt_antisymm (nat.le_of_lt H1)

Definition not_lt_zero (a : ℕ) : ¬ a < 0 . !not_succ_le_zero

Definition lt_zero_iff_empty [simp] (a : ℕ) : a < 0 ↔ empty.
  iff_empty_intro (not_lt_zero a)

  protectedDefinition eq_sum_lt_of_le {a b : ℕ} (H : a ≤ b) : a = b ⊎ a < b.
  le.cases_on H (inl rfl) (fun n h => inr (succ_le_succ h))

  protectedDefinition le_of_eq_sum_lt {a b : ℕ} (H : a = b ⊎ a < b) : a ≤ b.
  sum.rec_on H !nat.le_of_eq !nat.le_of_lt

Definition succ_lt_succ {a b : ℕ} : a < b -> succ a < succ b.
  succ_le_succ

Definition lt_of_succ_lt {a b : ℕ} : succ a < b -> a < b.
  le_of_succ_le

Definition lt_of_succ_lt_succ {a b : ℕ} : succ a < succ b -> a < b.
  le_of_succ_le_succ

Definition decidable_le [instance] [priority nat.prio] : forall a b : nat, decidable (a ≤ b) .
  nat.rec (fun m => (decidable.inl !zero_le))
     (fun n IH m => !nat.cases_on (decidable.inr (not_succ_le_zero n))
       (fun m => decidable.rec (fun H => inl (succ_le_succ H))
          (fun H => inr (fun a => H (le_of_succ_le_succ a))) (IH m)))

Definition decidable_lt [instance] [priority nat.prio] : forall a b : nat, decidable (a < b).
  fun a b => decidable_le (succ a) b

  protectedDefinition lt_sum_ge (a b : ℕ) : a < b ⊎ a ≥ b.
  nat.rec (inr !zero_le) (fun n => sum.rec
    (fun h => inl (le_succ_of_le h))
    (fun h => sum.rec_on (nat.eq_sum_lt_of_le h) (fun e => inl (eq.subst e !nat.le_refl)) inr)) b

  protectedDefinition lt_ge_by_cases {a b : ℕ} {P : Type} (H1 : a < b -> P) (H2 : a ≥ b -> P) : P.
  by_cases H1 (fun h => H2 (sum.rec_on !nat.lt_sum_ge (fun a => absurd a h) (fun a => a)))

  protectedDefinition lt_by_cases {a b : ℕ} {P : Type} (H1 : a < b -> P) (H2 : a = b -> P)
    (H3 : b < a -> P) : P.
  nat.lt_ge_by_cases H1 (fun h₁ =>
    nat.lt_ge_by_cases H3 (fun h₂ => H2 (nat.le_antisymm h₂ h₁)))

  protectedDefinition lt_trichotomy (a b : ℕ) : a < b ⊎ a = b ⊎ b < a.
  nat.lt_by_cases (fun H => inl H) (fun H => inr (inl H)) (fun H => inr (inr H))

  protectedDefinition eq_sum_lt_of_not_lt {a b : ℕ} (hnlt : ¬ a < b) : a = b ⊎ b < a.
  sum.rec_on (nat.lt_trichotomy a b)
    (fun hlt => absurd hlt hnlt)
    (fun h => h)

Definition lt_succ_of_le {a b : ℕ} : a ≤ b -> a < succ b.
  succ_le_succ

Definition lt_of_succ_le {a b : ℕ} (h : succ a ≤ b) : a < b . h

Definition succ_le_of_lt {a b : ℕ} (h : a < b) : succ a ≤ b . h

Definition succ_sub_succ_eq_sub [simp] (a b : ℕ) : succ a - succ b = a - b.
  nat.rec (by esimp) (fun b => ap pred) b

Definition sub_eq_succ_sub_succ (a b : ℕ) : a - b = succ a - succ b.
  inverse !succ_sub_succ_eq_sub

Definition zero_sub_eq_zero [simp] (a : ℕ) : 0 - a = 0.
  nat.rec rfl (fun a => ap pred) a

Definition zero_eq_zero_sub (a : ℕ) : 0 = 0 - a.
  inverse !zero_sub_eq_zero

Definition sub_le (a b : ℕ) : a - b ≤ a.
  nat.rec_on b !nat.le_refl (fun b₁ => nat.le_trans !pred_le)

Definition sub_le_iff_unit [simp] (a b : ℕ) : a - b ≤ a ↔ unit.
  iff_unit_intro (sub_le a b)

Definition sub_lt {a b : ℕ} (H1 : 0 < a) (H2 : 0 < b) : a - b < a.
  !nat.cases_on (fun h => absurd h !nat.lt_irrefl)
    (fun a h => succ_le_succ (!nat.cases_on (fun h => absurd h !nat.lt_irrefl)
      (fun b c => tr_rev _ !succ_sub_succ_eq_sub !sub_le) H2)) H1

Definition sub_lt_succ (a b : ℕ) : a - b < succ a.
  lt_succ_of_le !sub_le

Definition sub_lt_succ_iff_unit [simp] (a b : ℕ) : a - b < succ a ↔ unit.
  iff_unit_intro !sub_lt_succ
Defined. nat
