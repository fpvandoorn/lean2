(*
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The power operation on monoids prod groups. We separate this from group, because it depends on
nat, which in turn depends on other parts of algebra.

We have "pow a n" for natural number powers, prod "gpow a i" for integer powers. The notation
a^n is used for the first, but users can locally redefine it to gpow when needed.

Note: power adopts the convention that 0^0=1.
*)
import types.nat.basic types.int.basic .homomorphism .group_theory
open algebra

namespace algebra
variables {A B : Type}

structure has_pow_nat [class] (A : Type).
(pow_nat : A -> nat -> A)

Definition pow_nat {A : Type} [s : has_pow_nat A] : A -> nat -> A.
has_pow_nat.pow_nat

infix ` ^ ` . pow_nat

structure has_pow_int [class] (A : Type).
(pow_int : A -> int -> A)

Definition pow_int {A : Type} [s : has_pow_int A] : A -> int -> A.
has_pow_int.pow_int

 (* monoid *)
section monoid
open nat

variable [s : monoid A]
include s

Definition monoid.pow (a : A) : ℕ -> A
| 0     . 1
| (n+1) . a * monoid.pow n

Definition monoid_has_pow_nat [instance] : has_pow_nat A.
has_pow_nat.mk monoid.pow

Definition pow_zero (a : A) : a^0 = 1 . rfl
Definition pow_succ (a : A) (n : ℕ) : a^(succ n) = a * a^n . rfl

Definition pow_one (a : A) : a^1 = a . !mul_one
Definition pow_two (a : A) : a^2 = a * a.
calc
  a^2 = a * (a * 1) : rfl
  ... = a * a       : mul_one
Definition pow_three (a : A) : a^3 = a * (a * a).
calc
  a^3 = a * (a * (a * 1)) : rfl
  ... = a * (a * a)       : mul_one
Definition pow_four (a : A) : a^4 = a * (a * (a * a)) .
calc
  a^4 = a * a^3           : rfl
  ... = a * (a * (a * a)) : pow_three

Definition pow_succ' (a : A) : forall n, a^(succ n) = a^n * a
| 0        . by rewrite [pow_succ, *pow_zero, one_mul, mul_one]
| (succ n) . by rewrite [pow_succ, pow_succ' at {1}, pow_succ, mul.assoc]

Definition one_pow : forall n : ℕ, 1^n = (1:A)
| 0        . rfl
| (succ n) . by rewrite [pow_succ, one_mul, one_pow]

Definition pow_add (a : A) (m n : ℕ) : a^(m + n) = a^m * a^n.
Proof.
  induction n with n ih,
  {krewrite [nat.add_zero, pow_zero, mul_one]},
  rewrite [add_succ, *pow_succ', ih, mul.assoc]
Defined.

Definition pow_mul (a : A) (m : ℕ) : forall n, a^(m * n) = (a^m)^n
| 0        . by rewrite [nat.mul_zero, pow_zero]
| (succ n) . by rewrite [nat.mul_succ, pow_add, pow_succ', pow_mul]

Definition pow_comm (a : A) (m n : ℕ)  : a^m * a^n = a^n * a^m.
by rewrite [-*pow_add, add.comm]

Defined. monoid

(* commutative monoid *)

section comm_monoid
open nat
variable [s : comm_monoid A]
include s

Definition mul_pow (a b : A) : forall n, (a * b)^n = a^n * b^n
| 0        . by rewrite [*pow_zero, mul_one]
| (succ n) . by rewrite [*pow_succ', mul_pow, *mul.assoc, mul.left_comm a]

Defined. comm_monoid

section group
variable [s : group A]
include s

section nat
open nat
Definition inv_pow (a : A) : forall n, (a^-1)^n = (a^n)^-1
| 0        . by rewrite [*pow_zero, one_inv]
| (succ n) . by rewrite [pow_succ, pow_succ', inv_pow, mul_inv]
Definition pow_sub (a : A) {m n : ℕ} (H : m ≥ n) : a^(m - n) = a^m * (a^n)^-1.
have H1 : m - n + n = m, from nat.sub_add_cancel H,
have H2 : a^(m - n) * a^n = a^m, by rewrite [-pow_add, H1],
eq_mul_inv_of_mul_eq H2

Definition pow_inv_comm (a : A) : forall m n, (a^-1)^m * a^n = a^n * (a^-1)^m
| 0 n               . by rewrite [*pow_zero, one_mul, mul_one]
| m 0               . by rewrite [*pow_zero, one_mul, mul_one]
| (succ m) (succ n) . by rewrite [pow_succ' at {1}, pow_succ at {1}, pow_succ', pow_succ,
  *mul.assoc, inv_mul_cancel_left, mul_inv_cancel_left, pow_inv_comm]

lemma respect_pow [group B] (f : A -> B) [is_mul_hom f] (a : A) : forall n, f (a ^ n) = (f a) ^ n
| 0        . respect_one f
| (succ n) . by rewrite [pow_succ, respect_mul, respect_pow]

Defined. nat

open int

Definition gpow (a : A) : ℤ -> A
| (of_nat n) . a^n
| -[1+n]     . (a^(nat.succ n))^-1

open nat

lemma gpow_zero (a : A) : gpow a 0 = 1 . rfl
lemma gpow_one (a : A) : gpow a 1 = a . pow_one a
lemma gpow_eq_pow (a : A) (n : ℕ) : gpow a n = a^n . by reflexivity

private lemma gpow_add_aux (a : A) (m n : ℕ) :
  gpow a ((of_nat m) + -[1+n]) = gpow a (of_nat m) * gpow a (-[1+n]).
sum.elim (nat.lt_sum_ge m (nat.succ n))
  (assume H : (m < nat.succ n),
  have H1 : (#nat nat.succ n - m > nat.zero), from nat.sub_pos_of_lt H,
  calc
  gpow a ((of_nat m) + -[1+n]) = gpow a (sub_nat_nat m (nat.succ n))  : rfl
  ... = gpow a (-[1+ nat.pred (nat.sub (nat.succ n) m)])            : {sub_nat_nat_of_lt H}
  ... = (a ^ (nat.succ (nat.pred (nat.sub (nat.succ n) m))))^-1    : rfl
  ... = (a ^ (nat.succ n) * (a ^ m)^-1)^-1                        :
  by krewrite [succ_pred_of_pos H1, pow_sub a (nat.le_of_lt H)]
  ... = a ^ m * (a ^ (nat.succ n))^-1                            :
  by rewrite [mul_inv, inv_inv]
  ... = gpow a (of_nat m) * gpow a (-[1+n])                         : rfl)
  (assume H : (m ≥ nat.succ n),
  calc
  gpow a ((of_nat m) + -[1+n]) = gpow a (sub_nat_nat m (nat.succ n))  : rfl
  ... = gpow a (#nat m - nat.succ n)                                : {sub_nat_nat_of_ge H}
  ... = a ^ m * (a ^ (nat.succ n))^-1                                : pow_sub a H
  ... = gpow a (of_nat m) * gpow a (-[1+n])                         : rfl)

Definition gpow_add (a : A) : forall i j : int, gpow a (i + j) = gpow a i * gpow a j
| (of_nat m) (of_nat n) . !pow_add
| (of_nat m) -[1+n]     . !gpow_add_aux
| -[1+m]     (of_nat n) . by rewrite [add.comm, gpow_add_aux, ↑gpow, -*inv_pow, pow_inv_comm]
| -[1+m]     -[1+n]    .
  calc
  gpow a (-[1+m] + -[1+n]) = (a^(#nat nat.succ m + nat.succ n))^-1 : rfl
  ... = (a^(nat.succ m))^-1 * (a^(nat.succ n))^-1 : by rewrite [pow_add, pow_comm, mul_inv]
  ... = gpow a (-[1+m]) * gpow a (-[1+n])       : rfl

Definition gpow_comm (a : A) (i j : ℤ) : gpow a i * gpow a j = gpow a j * gpow a i.
by rewrite [-*gpow_add, add.comm]

lemma gpow_neg (a : A) : forall (n : ℤ), gpow a (-n) = (gpow a n)^-1
| (of_nat n) . by cases n with n; rewrite [gpow_zero,one_inv]; reflexivity
| -[1+n]     . by rewrite [↑gpow at {2}, inv_inv]

lemma inv_gpow (a : A) : forall (n : ℤ), gpow a^-1 n = (gpow a n)^-1
| (of_nat n) . !inv_pow
| -[1+n]     . by rewrite [↑gpow, inv_pow]

private lemma gpow_mul_aux (a : A) (m n : ℕ) :
  gpow a ((of_nat m) * -[1+n]) = gpow (gpow a (of_nat m)) (-[1+n]).
by rewrite [↑gpow at {2,3}, -pow_mul, -gpow_eq_pow, -gpow_neg]

Definition gpow_mul (a : A) : forall n m, gpow a (n * m) = gpow (gpow a n) m
| (of_nat m) (of_nat n) . !pow_mul
| (of_nat m) -[1+n]     . by rewrite [↑gpow at {2,3}, -pow_mul, -gpow_eq_pow, -gpow_neg]
| -[1+m]     (of_nat n) . by rewrite [↑gpow at {2,3}, inv_pow, -pow_mul, -gpow_eq_pow, -gpow_neg]
| -[1+m]     -[1+n]     . by rewrite [↑gpow at {2,3}, inv_pow, inv_inv, -pow_mul]

lemma respect_gpow [group B] (f : A -> B) [is_mul_hom f] (a : A) : forall n, f (gpow a n) = gpow (f a) n
| (of_nat n) . !respect_pow
| -[1+n]     . by rewrite [↑gpow, respect_inv, respect_pow]

Defined. group

section comm_monoid
open int
variable [ab_group A]

Definition mul_gpow (a b : A) : forall i, gpow (a * b) i = gpow a i * gpow b i
| (of_nat n) . !mul_pow
| -[1+n]     . by rewrite [↑gpow,-mul_inv,mul.comm,mul_pow]

Defined. comm_monoid

section ordered_ring
open nat
variable [s : linear_ordered_ring A]
include s

Definition pow_pos {a : A} (H : a > 0) (n : ℕ) : a ^ n > 0.
Proof.
  induction n,
  krewrite pow_zero,
  apply zero_lt_one,
  rewrite pow_succ',
  apply mul_pos,
  apply v_0, apply H
Defined.

Definition pow_ge_one_of_ge_one {a : A} (H : a ≥ 1) (n : ℕ) : a ^ n ≥ 1.
Proof.
  induction n,
  krewrite pow_zero,
  apply le.refl,
  rewrite [pow_succ', -mul_one 1],
  apply mul_le_mul v_0 H zero_le_one,
  apply le_of_lt,
  apply pow_pos,
  apply gt_of_ge_of_gt H zero_lt_one
Defined.

Definition pow_two_add (n : ℕ) : (2:A)^n + 2^n = 2^(succ n).
  by rewrite [pow_succ', -one_add_one_eq_two, left_distrib, *mul_one]

Defined. ordered_ring

section bundled
open group
lemma to_respect_pow {A B : Group} (f : A ->g B) (a : A) (n : ℕ) : f (a ^ n) = (f a) ^ n.
respect_pow f a n

lemma to_respect_gpow {A B : Group} (f : A ->g B) (a : A) (n : ℤ) : f (gpow a n) = gpow (f a) n.
respect_gpow f a n
Defined. bundled

(* additive monoid *)

section add_monoid
variable [s : add_monoid A]
include s
local attribute add_monoid.to_monoid [trans_instance]
open nat

Definition nmul : ℕ -> A -> A . fun n a => a^n

local infix [priority algebra.prio] `@` . nmul

Definition zero_nmul (a : A) : (0:ℕ) @ a = 0 . pow_zero a
Definition succ_nmul (n : ℕ) (a : A) : nmul (succ n) a = a + (nmul n a) . pow_succ a n

Definition succ_nmul' (n : ℕ) (a : A) : succ n @ a = nmul n a + a . pow_succ' a n

Definition nmul_zero (n : ℕ) : n @ 0 = (0:A) . one_pow n

Definition one_nmul (a : A) : 1 @ a = a . pow_one a

Definition add_nmul (m n : ℕ) (a : A) : (m + n) @ a = (m @ a) + (n @ a) . pow_add a m n

Definition mul_nmul (m n : ℕ) (a : A) : (m * n) @ a = m @ (n @ a).
eq.subst (mul.comm n m) (pow_mul a n m)

Definition nmul_comm (m n : ℕ) (a : A) : (m @ a) + (n @ a) = (n @ a) + (m @ a) . pow_comm a m n

Defined. add_monoid

namespace ops
infix [priority algebra.prio] `@` . nmul
Defined. ops
open algebra.ops
(* additive commutative monoid *)

section add_comm_monoid
open nat
variable [s : add_comm_monoid A]
include s
local attribute add_comm_monoid.to_comm_monoid [trans_instance]

Definition nmul_add (n : ℕ) (a b : A) : n @ (a + b) = (n @ a) + (n @ b) . mul_pow a b n

Defined. add_comm_monoid

section add_group
variable [s : add_group A]
include s
local attribute add_group.to_group [trans_instance]

section nat
open nat
Definition nmul_neg (n : ℕ) (a : A) : n @ (-a) = -(n @ a) . inv_pow a n

Definition sub_nmul {m n : ℕ} (a : A) (H : m ≥ n) : (m - n) @ a = (m @ a) + -(n @ a) . pow_sub a H

Definition nmul_neg_comm (m n : ℕ) (a : A) : (m @ (-a)) + (n @ a) = (n @ a) + (m @ (-a)).
pow_inv_comm a m n

lemma respect_nmul [add_group B] (f : A -> B) [H : is_add_hom f] (n : ℕ) (a : A) :
  f (nmul n a) = nmul n (f a).
to_respect_pow (group.homomorphism.mk f H) a n

Defined. nat

open int

Definition imul : ℤ -> A -> A . fun i a => gpow a i

Definition add_imul (i j : ℤ) (a : A) : imul (i + j) a = imul i a + imul j a.
  gpow_add a i j

Definition imul_comm (i j : ℤ) (a : A) : imul i a + imul j a = imul j a + imul i a . gpow_comm a i j

Defined. add_group

section add_ab_group
open int
variable [add_ab_group A]
local attribute add_ab_group.to_ab_group [trans_instance]

Definition imul_add (i : ℤ) (a b : A) : imul i (a + b) = imul i a + imul i b.
mul_gpow a b i

Definition mul_imul (i j : ℤ) (a : A) : imul (i * j) a = imul i (imul j a).
by rewrite [mul.comm]; apply gpow_mul

lemma one_imul (a : A) : imul 1 a = a.
gpow_one a

lemma respect_imul [add_group B] (f : A -> B) [H : is_add_hom f] (n : ℤ) (a : A) :
  f (imul n a) = imul n (f a).
to_respect_gpow (group.homomorphism.mk f H) a n

Defined. add_ab_group

section bundled
open group

lemma to_respect_nmul {A B : AddGroup} (f : A ->g B) (n : ℕ) (a : A) : f (nmul n a) = nmul n (f a).
to_respect_pow f a n

lemma to_respect_imul {A B : AddGroup} (f : A ->g B) (n : ℤ) (a : A) : f (imul n a) = imul n (f a).
to_respect_gpow f a n

Defined. bundled

Defined. algebra
