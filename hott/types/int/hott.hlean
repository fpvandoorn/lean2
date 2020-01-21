(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about the integers specific to HoTT
*)

import .order types.eq arity algebra.bundled
open core eq is_equiv equiv algebra is_trunc
open nat (hiding pred)

namespace int

  section
  open algebra
  (*
    we make these structures reducible, so that n * m in gℤ and agℤ can be interpreted as
    multiplication on ℤ. For this it's needed that the carriers of gℤ and agℤ reduce to ℤ unfolding
    only reducibleDefinitions.
  *)
Definition group_integers : AddGroup :=
  AddGroup.mk ℤ _

  notation `gℤ` := group_integers

Definition AbGroup_int : AddAbGroup :=
  AddAbGroup.mk ℤ _

  notation `agℤ` := AbGroup_int

Definition ring_int : Ring :=
  Ring.mk ℤ _

  notation `rℤ` := ring_int

Defined.

Definition is_equiv_succ [instance] : is_equiv succ :=
  adjointify succ pred (fun a => !add_sub_cancel) (fun a => !sub_add_cancel)
Definition equiv_succ : ℤ <~> ℤ := equiv.mk succ _

Definition is_equiv_neg [instance] : is_equiv (neg : ℤ -> ℤ) :=
  adjointify neg neg (fun x => !neg_neg) (fun a => !neg_neg)
Definition equiv_neg : ℤ <~> ℤ := equiv.mk neg _

Definition iiterate {A : Type} (f : A <~> A) (a : ℤ) : A <~> A :=
  rec_nat_on a erfl
               (fun b g => f @e g)
               (fun b g => g @e f^-1ᵉ)

Definition max0 : ℤ -> ℕ
  | (of_nat n) := n
  | (-[1+ n])  := 0

  lemma le_max0 : forall (n : ℤ), n ≤ of_nat (max0 n)
  | (of_nat n) := proof le.refl n qed
  | (-[1+ n])  := proof unit.star qed

  lemma le_of_max0_le {n : ℤ} {m : ℕ} (h : max0 n ≤ m) : n ≤ of_nat m :=
  le.trans (le_max0 n) (of_nat_le_of_nat_of_le h)

  (*Definition iterate_trans {A : Type} (f : A <~> A) (a : ℤ) *)
  (*   : iterate f a @e f = iterate f (a + 1) := *)
  (* sorry *)

  (*Definition trans_iterate {A : Type} (f : A <~> A) (a : ℤ) *)
  (*   : f @e iterate f a = iterate f (a + 1) := *)
  (* sorry *)

  (*Definition iterate_trans_symm {A : Type} (f : A <~> A) (a : ℤ) *)
  (*   : iterate f a @e f^-1e = iterate f (a - 1) := *)
  (* sorry *)

  (*Definition symm_trans_iterate {A : Type} (f : A <~> A) (a : ℤ) *)
  (*   : f^-1e @e iterate f a = iterate f (a - 1) := *)
  (* sorry *)

  (*Definition iterate_neg {A : Type} (f : A <~> A) (a : ℤ) *)
  (*   : iterate f (-a) = (iterate f a)^-1e := *)
  (* rec_nat_on a idp *)
  (*   (fun n p => calc *)
  (*     iterate f (-succ n) = iterate f (-n) @e f^-1e : rec_nat_on_neg *)
  (*       ... = (iterate f n)^-1e @e f^-1e : by rewrite p *)
  (*       ... = (f @e iterate f n)^-1e : sorry *)
  (*       ... = (iterate f (succ n))^-1e : idp) *)
  (*   sorry *)

  (*Definition iterate_add {A : Type} (f : A <~> A) (a b : ℤ) *)
  (*   : iterate f (a + b) = equiv.trans (iterate f a) (iterate f b) := *)
  (* sorry *)

  (*Definition iterate_sub {A : Type} (f : A <~> A) (a b : ℤ) *)
  (*   : iterate f (a - b) = equiv.trans (iterate f a) (equiv.symm (iterate f b)) := *)
  (* sorry *)

  (*Definition iterate_mul {A : Type} (f : A <~> A) (a b : ℤ) *)
  (*   : iterate f (a * b) = iterate (iterate f a) b := *)
  (* sorry *)

Defined. int open int



namespace eq
  variables {A : Type} {a : A} (p : a = a) (b c : ℤ) (n : ℕ)
Definition power : a = a :=
  rec_nat_on b idp
               (fun c q => q @ p)
               (fun c q => q @ p^-1)
  --iterate (equiv_eq_closed_right p a) b idp

  (*Definition power_neg_succ (n : ℕ) : power p (-succ n) = power p (-n) @ p^-1 := *)
  (* !rec_nat_on_neg *)

  (* local attribute nat.add int.add int.of_num nat.of_num int.succ *)

Definition power_con : power p b @ p = power p (succ b) :=
  rec_nat_on b
    idp
    (fun n IH => idp)
    (fun n IH => calc
      power p (-succ n) @ p
            = (power p (-int.of_nat n) @ p^-1) @ p : by krewrite [↑power,rec_nat_on_neg]
        ... = power p (-int.of_nat n) : inv_con_cancel_right
        ... = power p (succ (-succ n)) : by rewrite -succ_neg_succ)

Definition power_con_inv : power p b @ p^-1 = power p (pred b) :=
  rec_nat_on b
    idp
    (fun n IH => calc
      power p (succ n) @ p^-1 = power p n : by apply con_inv_cancel_right
        ... = power p (pred (succ n))   : by rewrite pred_nat_succ)
    (fun n IH => calc
      power p (-int.of_nat (succ n)) @ p^-1
            = power p (-int.of_nat (succ (succ n))) : by krewrite [↑power,*rec_nat_on_neg]
        ... = power p (pred (-succ n)) : by rewrite -neg_succ)

Definition con_power : p @ power p b = power p (succ b) :=
  rec_nat_on b
  ( by rewrite ↑[power];exact (concat_1p _)^-1)
  ( fun n IH => proof calc
    p @ power p (succ n) = (p @ power p n) @ p : con.assoc p _ p
      ... = power p (succ (succ n)) : by rewrite IH qed)
  ( fun n IH => calc
          p @ power p (-int.of_nat (succ n))
                = p @ (power p (-int.of_nat n) @ p^-1) : by rewrite [↑power, rec_nat_on_neg]
            ... = (p @ power p (-int.of_nat n)) @ p^-1 : con.assoc
            ... = power p (succ (-int.of_nat n)) @ p^-1 : by rewrite IH
            ... = power p (pred (succ (-int.of_nat n))) : power_con_inv
            ... = power p (succ (-int.of_nat (succ n))) : by rewrite [succ_neg_nat_succ,int.pred_succ])

Definition inv_con_power : p^-1 @ power p b = power p (pred b) :=
  rec_nat_on b
  ( by rewrite ↑[power];exact (concat_1p _)^-1)
  (fun n IH => calc
    p^-1 @ power p (succ n) = p^-1 @ power p n @ p : con.assoc
      ... = power p (pred n) @ p : by rewrite IH
      ... = power p (succ (pred n)) : power_con
      ... = power p (pred (succ n)) : by rewrite [succ_pred,-int.pred_succ n])
  ( fun n IH => calc
    p^-1 @ power p (-int.of_nat (succ n))
          = p^-1 @ (power p (-int.of_nat n) @ p^-1) : by rewrite [↑power,rec_nat_on_neg]
      ... = (p^-1 @ power p (-int.of_nat n)) @ p^-1 : con.assoc
      ... = power p (pred (-int.of_nat n)) @ p^-1 : by rewrite IH
      ... = power p (-int.of_nat (succ n)) @ p^-1 : by rewrite -neg_succ
      ... = power p (-succ (succ n)) : by krewrite [↑power,*rec_nat_on_neg]
      ... = power p (pred (-succ n)) : by rewrite -neg_succ)

Definition power_con_power : forall (b : ℤ), power p b @ power p c = power p (b + c) :=
  rec_nat_on c
    (fun b => by rewrite int.add_zero)
    (fun n IH b => by rewrite [-con_power,-con.assoc,power_con,IH,↑succ,add.assoc,
                          add.comm (int.of_nat n)])
    (fun n IH b => by rewrite [neg_nat_succ,-inv_con_power,-con.assoc,power_con_inv,IH,↑pred,
                          +sub_eq_add_neg,add.assoc,add.comm (-n)])

Defined. eq
