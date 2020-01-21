(*
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Partially ordered additive groups, modeled on Isabelle's library. These classes can be refined
if necessary.
*)
import algebra.group algebra.order
open eq eq.ops algebra   (* note: ^-1 will be overloaded *)
set_option class.force_new true

variable {A : Type}

(* partially ordered monoids, such as the natural numbers *)

namespace algebra
structure ordered_mul_cancel_comm_monoid [class] (A : Type) extends comm_monoid A,
 left_cancel_semigroup A, right_cancel_semigroup A, order_pair A.
(mul_le_mul_left : forall a b, le a b -> forall c, le (mul c a) (mul c b))
(le_of_mul_le_mul_left : forall a b c, le (mul a b) (mul a c) -> le b c)
(mul_lt_mul_left : forall a b, lt a b -> forall c, lt (mul c a) (mul c b))
(lt_of_mul_lt_mul_left : forall a b c, lt (mul a b) (mul a c) -> lt b c)

Definition ordered_cancel_comm_monoid [class] : Type -> Type . ordered_mul_cancel_comm_monoid

Definition add_comm_monoid_of_ordered_cancel_comm_monoid [trans_instance]
  (A : Type) [H : ordered_cancel_comm_monoid A] : add_comm_monoid A.
@ordered_mul_cancel_comm_monoid.to_comm_monoid A H

Definition add_left_cancel_semigroup_of_ordered_cancel_comm_monoid [trans_instance]
  (A : Type) [H : ordered_cancel_comm_monoid A] : add_left_cancel_semigroup A.
@ordered_mul_cancel_comm_monoid.to_left_cancel_semigroup A H

Definition add_right_cancel_semigroup_of_ordered_cancel_comm_monoid [trans_instance]
  (A : Type) [H : ordered_cancel_comm_monoid A] : add_right_cancel_semigroup A.
@ordered_mul_cancel_comm_monoid.to_right_cancel_semigroup A H

Definition order_pair_of_ordered_cancel_comm_monoid [trans_instance]
  (A : Type) [H : ordered_cancel_comm_monoid A] : order_pair A.
@ordered_mul_cancel_comm_monoid.to_order_pair A H

section
  variables [s : ordered_cancel_comm_monoid A]
  variables {a b c d e : A}
  include s

Definition add_lt_add_left (H : a < b) (c : A) : c + a < c + b.
  @ordered_mul_cancel_comm_monoid.mul_lt_mul_left A s a b H c

Definition add_lt_add_right (H : a < b) (c : A) : a + c < b + c.
Proof.
  rewrite [add.comm, {b + _}add.comm],
  exact (add_lt_add_left H c)
Defined.

Definition add_le_add_left (H : a ≤ b) (c : A) : c + a ≤ c + b.
  @ordered_mul_cancel_comm_monoid.mul_le_mul_left A s a b H c

Definition add_le_add_right (H : a ≤ b) (c : A) : a + c ≤ b + c.
  (add.comm c a) # (add.comm c b) # (add_le_add_left H c)

Definition add_le_add (Hab : a ≤ b) (Hcd : c ≤ d) : a + c ≤ b + d.
  le.trans (add_le_add_right Hab c) (add_le_add_left Hcd b)

Definition le_add_of_nonneg_right (H : b ≥ 0) : a ≤ a + b.
Proof.
  have H1 : a + b ≥ a + 0, from add_le_add_left H a,
  rewrite add_zero at H1,
  exact H1
Defined.

Definition le_add_of_nonneg_left (H : b ≥ 0) : a ≤ b + a.
Proof.
  have H1 : 0 + a ≤ b + a, from add_le_add_right H a,
  rewrite zero_add at H1,
  exact H1
Defined.

Definition add_lt_add (Hab : a < b) (Hcd : c < d) : a + c < b + d.
  lt.trans (add_lt_add_right Hab c) (add_lt_add_left Hcd b)

Definition add_lt_add_of_le_of_lt (Hab : a ≤ b) (Hcd : c < d) : a + c < b + d.
  lt_of_le_of_lt (add_le_add_right Hab c) (add_lt_add_left Hcd b)

Definition add_lt_add_of_lt_of_le (Hab : a < b) (Hcd : c ≤ d) : a + c < b + d.
  lt_of_lt_of_le (add_lt_add_right Hab c) (add_le_add_left Hcd b)

Definition lt_add_of_pos_right (H : b > 0) : a < a + b . !add_zero # add_lt_add_left H a

Definition lt_add_of_pos_left (H : b > 0) : a < b + a . !zero_add # add_lt_add_right H a

  (* here we start using le_of_add_le_add_left. *)
Definition le_of_add_le_add_left (H : a + b ≤ a + c) : b ≤ c.
  @ordered_mul_cancel_comm_monoid.le_of_mul_le_mul_left A s a b c H

Definition le_of_add_le_add_right (H : a + b ≤ c + b) : a ≤ c.
  le_of_add_le_add_left (show b + a ≤ b + c, begin rewrite [add.comm, {b + _}add.comm], exact H end)

Definition lt_of_add_lt_add_left (H : a + b < a + c) : b < c.
  @ordered_mul_cancel_comm_monoid.lt_of_mul_lt_mul_left A s a b c H

Definition lt_of_add_lt_add_right (H : a + b < c + b) : a < c.
  lt_of_add_lt_add_left ((add.comm a b) # (add.comm c b) # H)

Definition add_le_add_left_iff (a b c : A) : a + b ≤ a + c ↔ b ≤ c.
  iff.intro le_of_add_le_add_left (assume H, add_le_add_left H _)

Definition add_le_add_right_iff (a b c : A) : a + b ≤ c + b ↔ a ≤ c.
  iff.intro le_of_add_le_add_right (assume H, add_le_add_right H _)

Definition add_lt_add_left_iff (a b c : A) : a + b < a + c ↔ b < c.
  iff.intro lt_of_add_lt_add_left (assume H, add_lt_add_left H _)

Definition add_lt_add_right_iff (a b c : A) : a + b < c + b ↔ a < c.
  iff.intro lt_of_add_lt_add_right (assume H, add_lt_add_right H _)

  (* here we start using properties of zero. *)
Definition add_nonneg (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a + b.
  !zero_add # (add_le_add Ha Hb)

Definition add_pos (Ha : 0 < a) (Hb : 0 < b) : 0 < a + b.
  !zero_add # (add_lt_add Ha Hb)

Definition add_pos_of_pos_of_nonneg (Ha : 0 < a) (Hb : 0 ≤ b) : 0 < a + b.
  !zero_add # (add_lt_add_of_lt_of_le Ha Hb)

Definition add_pos_of_nonneg_of_pos (Ha : 0 ≤ a) (Hb : 0 < b) : 0 < a + b.
  !zero_add # (add_lt_add_of_le_of_lt Ha Hb)

Definition add_nonpos (Ha : a ≤ 0) (Hb : b ≤ 0) : a + b ≤ 0.
  !zero_add # (add_le_add Ha Hb)

Definition add_neg (Ha : a < 0) (Hb : b < 0) : a + b < 0.
  !zero_add # (add_lt_add Ha Hb)

Definition add_neg_of_neg_of_nonpos (Ha : a < 0) (Hb : b ≤ 0) : a + b < 0.
  !zero_add # (add_lt_add_of_lt_of_le Ha Hb)

Definition add_neg_of_nonpos_of_neg (Ha : a ≤ 0) (Hb : b < 0) : a + b < 0.
  !zero_add # (add_lt_add_of_le_of_lt Ha Hb)

  (* TODO: add nonpos version (will be easier with simplifier) *)
Definition add_eq_zero_iff_eq_zero_prod_eq_zero_of_nonneg_of_nonneg
  (Ha : 0 ≤ a) (Hb : 0 ≤ b) : a + b = 0 ↔ a = 0 \* b = 0.
  iff.intro
  (assume Hab : a + b = 0,
  have Ha' : a ≤ 0, from
  calc
  a     = a + 0 : by rewrite add_zero
  ... ≤ a + b : add_le_add_left Hb
  ... = 0     : Hab,
  have Haz : a = 0, from le.antisymm Ha' Ha,
  have Hb' : b ≤ 0, from
  calc
  b     = 0 + b : by rewrite zero_add
  ... ≤ a + b : by exact add_le_add_right Ha _
  ... = 0     : Hab,
  have Hbz : b = 0, from le.antisymm Hb' Hb,
  pair Haz Hbz)
  (assume Hab : a = 0 \* b = 0,
  obtain Ha' Hb', from Hab,
  by rewrite [Ha', Hb', add_zero])

Definition le_add_of_nonneg_of_le (Ha : 0 ≤ a) (Hbc : b ≤ c) : b ≤ a + c.
  !zero_add # add_le_add Ha Hbc

Definition le_add_of_le_of_nonneg (Hbc : b ≤ c) (Ha : 0 ≤ a) : b ≤ c + a.
  !add_zero # add_le_add Hbc Ha

Definition lt_add_of_pos_of_le (Ha : 0 < a) (Hbc : b ≤ c) : b < a + c.
  !zero_add # add_lt_add_of_lt_of_le Ha Hbc

Definition lt_add_of_le_of_pos (Hbc : b ≤ c) (Ha : 0 < a) : b < c + a.
  !add_zero # add_lt_add_of_le_of_lt Hbc Ha

Definition add_le_of_nonpos_of_le (Ha : a ≤ 0) (Hbc : b ≤ c) : a + b ≤ c.
  !zero_add # add_le_add Ha Hbc

Definition add_le_of_le_of_nonpos (Hbc : b ≤ c) (Ha : a ≤ 0) : b + a ≤ c.
  !add_zero # add_le_add Hbc Ha

Definition add_lt_of_neg_of_le (Ha : a < 0) (Hbc : b ≤ c) : a + b < c.
  !zero_add # add_lt_add_of_lt_of_le Ha Hbc

Definition add_lt_of_le_of_neg (Hbc : b ≤ c) (Ha : a < 0) : b + a < c.
  !add_zero # add_lt_add_of_le_of_lt Hbc Ha

Definition lt_add_of_nonneg_of_lt (Ha : 0 ≤ a) (Hbc : b < c) : b < a + c.
  !zero_add # add_lt_add_of_le_of_lt Ha Hbc

Definition lt_add_of_lt_of_nonneg (Hbc : b < c) (Ha : 0 ≤ a) : b < c + a.
  !add_zero # add_lt_add_of_lt_of_le Hbc Ha

Definition lt_add_of_pos_of_lt (Ha : 0 < a) (Hbc : b < c) : b < a + c.
  !zero_add # add_lt_add Ha Hbc

Definition lt_add_of_lt_of_pos (Hbc : b < c) (Ha : 0 < a) : b < c + a.
  !add_zero # add_lt_add Hbc Ha

Definition add_lt_of_nonpos_of_lt (Ha : a ≤ 0) (Hbc : b < c) : a + b < c.
  !zero_add # add_lt_add_of_le_of_lt Ha Hbc

Definition add_lt_of_lt_of_nonpos (Hbc : b < c) (Ha : a ≤ 0)  : b + a < c.
  !add_zero # add_lt_add_of_lt_of_le Hbc Ha

Definition add_lt_of_neg_of_lt (Ha : a < 0) (Hbc : b < c) : a + b < c.
  !zero_add # add_lt_add Ha Hbc

Definition add_lt_of_lt_of_neg (Hbc : b < c) (Ha : a < 0) : b + a < c.
  !add_zero # add_lt_add Hbc Ha
Defined.

(* partially ordered groups *)

structure ordered_mul_ab_group [class] (A : Type) extends ab_group A, order_pair A.
(mul_le_mul_left : forall a b, le a b -> forall c, le (mul c a) (mul c b))
(mul_lt_mul_left : forall a b, lt a b -> forall c, lt (mul c a) (mul c b))

Definition ordered_ab_group [class] : Type -> Type . ordered_mul_ab_group

Definition add_ab_group_of_ordered_ab_group [trans_instance] (A : Type)
  [H : ordered_ab_group A] : add_ab_group A.
@ordered_mul_ab_group.to_ab_group A H

Definition ordered_mul_ab_group.le_of_mul_le_mul_left [s : ordered_mul_ab_group A] {a b c : A}
  (H : a * b ≤ a * c) : b ≤ c.
have H' : a^-1 * (a * b) ≤ a^-1 * (a * c), from ordered_mul_ab_group.mul_le_mul_left _ _ H _,
by rewrite *inv_mul_cancel_left at H'; exact H'

Definition ordered_mul_ab_group.lt_of_mul_lt_mul_left [s : ordered_mul_ab_group A] {a b c : A}
  (H : a * b < a * c) : b < c.
have H' : a^-1 * (a * b) < a^-1 * (a * c), from ordered_mul_ab_group.mul_lt_mul_left _ _ H _,
by rewrite *inv_mul_cancel_left at H'; exact H'

Definition ordered_mul_ab_group.to_ordered_mul_cancel_comm_monoid [trans_instance]
  [s : ordered_mul_ab_group A] : ordered_mul_cancel_comm_monoid A.
( ordered_mul_cancel_comm_monoid, s,
  mul_left_cancel       . @mul.left_cancel A _,
  mul_right_cancel      . @mul.right_cancel A _,
  le_of_mul_le_mul_left . @ordered_mul_ab_group.le_of_mul_le_mul_left A _,
  lt_of_mul_lt_mul_left . @ordered_mul_ab_group.lt_of_mul_lt_mul_left A _)

Definition ordered_ab_group.to_ordered_cancel_comm_monoid [trans_instance]
  [s : ordered_ab_group A] : ordered_cancel_comm_monoid A.
@ordered_mul_ab_group.to_ordered_mul_cancel_comm_monoid A s

section
  variables [s : ordered_ab_group A] (a b c d e : A)
  include s

Definition neg_le_neg {a b : A} (H : a ≤ b) : -b ≤ -a.
  have H1 : 0 ≤ -a + b, from !add.left_inv # !(add_le_add_left H),
  !add_neg_cancel_right # !zero_add # add_le_add_right H1 (-b)

Definition le_of_neg_le_neg {a b : A} (H : -b ≤ -a) : a ≤ b.
  neg_neg a # neg_neg b # neg_le_neg H

Definition neg_le_neg_iff_le : -a ≤ -b ↔ b ≤ a.
  iff.intro le_of_neg_le_neg neg_le_neg

Definition nonneg_of_neg_nonpos {a : A} (H : -a ≤ 0) : 0 ≤ a.
  le_of_neg_le_neg (neg_zero^-1 # H)

Definition neg_nonpos_of_nonneg {a : A} (H : 0 ≤ a) : -a ≤ 0.
  neg_zero # neg_le_neg H

Definition neg_nonpos_iff_nonneg : -a ≤ 0 ↔ 0 ≤ a.
  iff.intro nonneg_of_neg_nonpos neg_nonpos_of_nonneg

Definition nonpos_of_neg_nonneg {a : A} (H : 0 ≤ -a) : a ≤ 0.
  le_of_neg_le_neg (neg_zero^-1 # H)

Definition neg_nonneg_of_nonpos {a : A} (H : a ≤ 0) : 0 ≤ -a.
  neg_zero # neg_le_neg H

Definition neg_nonneg_iff_nonpos : 0 ≤ -a ↔ a ≤ 0.
  iff.intro nonpos_of_neg_nonneg neg_nonneg_of_nonpos

Definition neg_lt_neg {a b : A} (H : a < b) : -b < -a.
  have H1 : 0 < -a + b, from !add.left_inv # !(add_lt_add_left H),
  !add_neg_cancel_right # !zero_add # add_lt_add_right H1 (-b)

Definition lt_of_neg_lt_neg {a b : A} (H : -b < -a) : a < b.
  neg_neg a # neg_neg b # neg_lt_neg H

Definition neg_lt_neg_iff_lt : -a < -b ↔ b < a.
  iff.intro lt_of_neg_lt_neg neg_lt_neg

Definition pos_of_neg_neg {a : A} (H : -a < 0) : 0 < a.
  lt_of_neg_lt_neg (neg_zero^-1 # H)

Definition neg_neg_of_pos {a : A} (H : 0 < a) : -a < 0.
  neg_zero # neg_lt_neg H

Definition neg_neg_iff_pos : -a < 0 ↔ 0 < a.
  iff.intro pos_of_neg_neg neg_neg_of_pos

Definition neg_of_neg_pos {a : A} (H : 0 < -a) : a < 0.
  lt_of_neg_lt_neg (neg_zero^-1 # H)

Definition neg_pos_of_neg {a : A} (H : a < 0) : 0 < -a.
  neg_zero # neg_lt_neg H

Definition neg_pos_iff_neg : 0 < -a ↔ a < 0.
  iff.intro neg_of_neg_pos neg_pos_of_neg

Definition le_neg_iff_le_neg : a ≤ -b ↔ b ≤ -a . !neg_neg # !neg_le_neg_iff_le

Definition le_neg_of_le_neg {a b : A} : a ≤ -b -> b ≤ -a . iff.mp !le_neg_iff_le_neg

Definition neg_le_iff_neg_le : -a ≤ b ↔ -b ≤ a . !neg_neg # !neg_le_neg_iff_le

Definition neg_le_of_neg_le {a b : A} : -a ≤ b -> -b ≤ a . iff.mp !neg_le_iff_neg_le

Definition lt_neg_iff_lt_neg : a < -b ↔ b < -a . !neg_neg # !neg_lt_neg_iff_lt

Definition lt_neg_of_lt_neg {a b : A} : a < -b -> b < -a . iff.mp !lt_neg_iff_lt_neg

Definition neg_lt_iff_neg_lt : -a < b ↔ -b < a . !neg_neg # !neg_lt_neg_iff_lt

Definition neg_lt_of_neg_lt {a b : A} : -a < b -> -b < a . iff.mp !neg_lt_iff_neg_lt

Definition sub_nonneg_iff_le : 0 ≤ a - b ↔ b ≤ a . !sub_self # !add_le_add_right_iff

Definition sub_nonneg_of_le {a b : A} : b ≤ a -> 0 ≤ a - b . iff.mpr !sub_nonneg_iff_le

Definition le_of_sub_nonneg {a b : A} : 0 ≤ a - b -> b ≤ a . iff.mp !sub_nonneg_iff_le

Definition sub_nonpos_iff_le : a - b ≤ 0 ↔ a ≤ b . !sub_self # !add_le_add_right_iff

Definition sub_nonpos_of_le {a b : A} : a ≤ b -> a - b ≤ 0 . iff.mpr !sub_nonpos_iff_le

Definition le_of_sub_nonpos {a b : A} : a - b ≤ 0 -> a ≤ b . iff.mp !sub_nonpos_iff_le

Definition sub_pos_iff_lt : 0 < a - b ↔ b < a . !sub_self # !add_lt_add_right_iff

Definition sub_pos_of_lt {a b : A} : b < a -> 0 < a - b . iff.mpr !sub_pos_iff_lt

Definition lt_of_sub_pos {a b : A} : 0 < a - b -> b < a . iff.mp !sub_pos_iff_lt

Definition sub_neg_iff_lt : a - b < 0 ↔ a < b . !sub_self # !add_lt_add_right_iff

Definition sub_neg_of_lt {a b : A} : a < b -> a - b < 0 . iff.mpr !sub_neg_iff_lt

Definition lt_of_sub_neg {a b : A} : a - b < 0 -> a < b . iff.mp !sub_neg_iff_lt

Definition add_le_iff_le_neg_add : a + b ≤ c ↔ b ≤ -a + c.
  have H: a + b ≤ c ↔ -a + (a + b) ≤ -a + c, from iff.symm (!add_le_add_left_iff),
  !neg_add_cancel_left # H

Definition add_le_of_le_neg_add {a b c : A} : b ≤ -a + c -> a + b ≤ c.
  iff.mpr !add_le_iff_le_neg_add

Definition le_neg_add_of_add_le {a b c : A} : a + b ≤ c -> b ≤ -a + c.
  iff.mp !add_le_iff_le_neg_add

Definition add_le_iff_le_sub_left : a + b ≤ c ↔ b ≤ c - a.
  by rewrite [sub_eq_add_neg, {c+_}add.comm]; apply add_le_iff_le_neg_add

Definition add_le_of_le_sub_left {a b c : A} : b ≤ c - a -> a + b ≤ c.
  iff.mpr !add_le_iff_le_sub_left

Definition le_sub_left_of_add_le {a b c : A} : a + b ≤ c -> b ≤ c - a.
  iff.mp !add_le_iff_le_sub_left

Definition add_le_iff_le_sub_right : a + b ≤ c ↔ a ≤ c - b.
  have H: a + b ≤ c ↔ a + b - b ≤ c - b, from iff.symm (!add_le_add_right_iff),
  !add_neg_cancel_right # H

Definition add_le_of_le_sub_right {a b c : A} : a ≤ c - b -> a + b ≤ c.
  iff.mpr !add_le_iff_le_sub_right

Definition le_sub_right_of_add_le {a b c : A} : a + b ≤ c -> a ≤ c - b.
  iff.mp !add_le_iff_le_sub_right

Definition le_add_iff_neg_add_le : a ≤ b + c ↔ -b + a ≤ c.
  have H: a ≤ b + c ↔ -b + a ≤ -b + (b + c), from iff.symm (!add_le_add_left_iff),
  by rewrite neg_add_cancel_left at H; exact H

Definition le_add_of_neg_add_le {a b c : A} : -b + a ≤ c -> a ≤ b + c.
  iff.mpr !le_add_iff_neg_add_le

Definition neg_add_le_of_le_add {a b c : A} : a ≤ b + c -> -b + a ≤ c.
  iff.mp !le_add_iff_neg_add_le

Definition le_add_iff_sub_left_le : a ≤ b + c ↔ a - b ≤ c.
  by rewrite [sub_eq_add_neg, {a+_}add.comm]; apply le_add_iff_neg_add_le

Definition le_add_of_sub_left_le {a b c : A} : a - b ≤ c -> a ≤ b + c.
  iff.mpr !le_add_iff_sub_left_le

Definition sub_left_le_of_le_add {a b c : A} : a ≤ b + c -> a - b ≤ c.
  iff.mp !le_add_iff_sub_left_le

Definition le_add_iff_sub_right_le : a ≤ b + c ↔ a - c ≤ b.
  have H: a ≤ b + c ↔ a - c ≤ b + c - c, from iff.symm (!add_le_add_right_iff),
  by rewrite [sub_eq_add_neg (b+c) c at H, add_neg_cancel_right at H]; exact H

Definition le_add_of_sub_right_le {a b c : A} : a - c ≤ b -> a ≤ b + c.
  iff.mpr !le_add_iff_sub_right_le

Definition sub_right_le_of_le_add {a b c : A} : a ≤ b + c -> a - c ≤ b.
  iff.mp !le_add_iff_sub_right_le

Definition le_add_iff_neg_add_le_left : a ≤ b + c ↔ -b + a ≤ c.
  have H: a ≤ b + c ↔ -b + a ≤ -b + (b + c), from iff.symm (!add_le_add_left_iff),
  by rewrite neg_add_cancel_left at H; exact H

Definition le_add_of_neg_add_le_left {a b c : A} : -b + a ≤ c -> a ≤ b + c.
  iff.mpr !le_add_iff_neg_add_le_left

Definition neg_add_le_left_of_le_add {a b c : A} : a ≤ b + c -> -b + a ≤ c.
  iff.mp !le_add_iff_neg_add_le_left

Definition le_add_iff_neg_add_le_right : a ≤ b + c ↔ -c + a ≤ b.
  by rewrite add.comm; apply le_add_iff_neg_add_le_left

Definition le_add_of_neg_add_le_right {a b c : A} : -c + a ≤ b -> a ≤ b + c.
  iff.mpr !le_add_iff_neg_add_le_right

Definition neg_add_le_right_of_le_add {a b c : A} : a ≤ b + c -> -c + a ≤ b.
  iff.mp  !le_add_iff_neg_add_le_right

Definition le_add_iff_neg_le_sub_left : c ≤ a + b ↔ -a ≤ b - c.
  have H : c ≤ a + b ↔ -a + c ≤ b, from !le_add_iff_neg_add_le,
  have H' : -a + c ≤ b ↔ -a ≤ b - c, from !add_le_iff_le_sub_right,
  iff.trans H H'

Definition le_add_of_neg_le_sub_left {a b c : A} : -a ≤ b - c -> c ≤ a + b.
  iff.mpr !le_add_iff_neg_le_sub_left

Definition neg_le_sub_left_of_le_add {a b c : A} : c ≤ a + b -> -a ≤ b - c.
  iff.mp !le_add_iff_neg_le_sub_left

Definition le_add_iff_neg_le_sub_right : c ≤ a + b ↔ -b ≤ a - c.
  by rewrite add.comm; apply le_add_iff_neg_le_sub_left

Definition le_add_of_neg_le_sub_right {a b c : A} : -b ≤ a - c -> c ≤ a + b.
  iff.mpr !le_add_iff_neg_le_sub_right

Definition neg_le_sub_right_of_le_add {a b c : A} : c ≤ a + b -> -b ≤ a - c.
  iff.mp !le_add_iff_neg_le_sub_right

Definition add_lt_iff_lt_neg_add_left : a + b < c ↔ b < -a + c.
  have H: a + b < c ↔ -a + (a + b) < -a + c, from iff.symm (!add_lt_add_left_iff),
Proof. rewrite neg_add_cancel_left at H, exact H end

Definition add_lt_of_lt_neg_add_left {a b c : A} : b < -a + c -> a + b < c.
  iff.mpr !add_lt_iff_lt_neg_add_left

Definition lt_neg_add_left_of_add_lt {a b c : A} : a + b < c -> b < -a + c.
  iff.mp !add_lt_iff_lt_neg_add_left

Definition add_lt_iff_lt_neg_add_right : a + b < c ↔ a < -b + c.
  by rewrite add.comm; apply add_lt_iff_lt_neg_add_left

Definition add_lt_of_lt_neg_add_right {a b c : A} : a < -b + c -> a + b < c.
  iff.mpr !add_lt_iff_lt_neg_add_right

Definition lt_neg_add_right_of_add_lt {a b c : A} : a + b < c -> a < -b + c.
  iff.mp !add_lt_iff_lt_neg_add_right

Definition add_lt_iff_lt_sub_left : a + b < c ↔ b < c - a.
Proof.
  rewrite [sub_eq_add_neg, {c+_}add.comm],
  apply add_lt_iff_lt_neg_add_left
Defined.

Definition add_lt_of_lt_sub_left {a b c : A} : b < c - a -> a + b < c.
  iff.mpr !add_lt_iff_lt_sub_left

Definition lt_sub_left_of_add_lt {a b c : A} : a + b < c -> b < c - a.
  iff.mp !add_lt_iff_lt_sub_left

Definition add_lt_iff_lt_sub_right : a + b < c ↔ a < c - b.
  have H: a + b < c ↔ a + b - b < c - b, from iff.symm (!add_lt_add_right_iff),
  by rewrite [sub_eq_add_neg at H, add_neg_cancel_right at H]; exact H

Definition add_lt_of_lt_sub_right {a b c : A} : a < c - b -> a + b < c.
  iff.mpr !add_lt_iff_lt_sub_right

Definition lt_sub_right_of_add_lt {a b c : A} : a + b < c -> a < c - b.
  iff.mp !add_lt_iff_lt_sub_right

Definition lt_add_iff_neg_add_lt_left : a < b + c ↔ -b + a < c.
  have H: a < b + c ↔ -b + a < -b + (b + c), from iff.symm (!add_lt_add_left_iff),
  by rewrite neg_add_cancel_left at H; exact H

Definition lt_add_of_neg_add_lt_left {a b c : A} : -b + a < c -> a < b + c.
  iff.mpr !lt_add_iff_neg_add_lt_left

Definition neg_add_lt_left_of_lt_add {a b c : A} : a < b + c -> -b + a < c.
  iff.mp !lt_add_iff_neg_add_lt_left

Definition lt_add_iff_neg_add_lt_right : a < b + c ↔ -c + a < b.
  by rewrite add.comm; apply lt_add_iff_neg_add_lt_left

Definition lt_add_of_neg_add_lt_right {a b c : A} : -c + a < b -> a < b + c.
  iff.mpr !lt_add_iff_neg_add_lt_right

Definition neg_add_lt_right_of_lt_add {a b c : A} : a < b + c -> -c + a < b.
  iff.mp !lt_add_iff_neg_add_lt_right

Definition lt_add_iff_sub_lt_left : a < b + c ↔ a - b < c.
  by rewrite [sub_eq_add_neg, {a + _}add.comm]; apply lt_add_iff_neg_add_lt_left

Definition lt_add_of_sub_lt_left {a b c : A} : a - b < c -> a < b + c.
  iff.mpr !lt_add_iff_sub_lt_left

Definition sub_lt_left_of_lt_add {a b c : A} : a < b + c -> a - b < c.
  iff.mp !lt_add_iff_sub_lt_left

Definition lt_add_iff_sub_lt_right : a < b + c ↔ a - c < b.
  by rewrite add.comm; apply lt_add_iff_sub_lt_left

Definition lt_add_of_sub_lt_right {a b c : A} : a - c < b -> a < b + c.
  iff.mpr !lt_add_iff_sub_lt_right

Definition sub_lt_right_of_lt_add {a b c : A} : a < b + c -> a - c < b.
  iff.mp !lt_add_iff_sub_lt_right

Definition sub_lt_of_sub_lt {a b c : A} : a - b < c -> a - c < b.
Proof.
  intro H,
  apply sub_lt_left_of_lt_add,
  apply lt_add_of_sub_lt_right H
Defined.

Definition sub_le_of_sub_le {a b c : A} : a - b ≤ c -> a - c ≤ b.
Proof.
  intro H,
  apply sub_left_le_of_le_add,
  apply le_add_of_sub_right_le H
Defined.

  (* TODO: the Isabelle library has varations on a + b ≤ b ↔ a ≤ 0 *)
Definition le_iff_le_of_sub_eq_sub {a b c d : A} (H : a - b = c - d) : a ≤ b ↔ c ≤ d.
  calc
  a ≤ b ↔ a - b ≤ 0   : iff.symm (sub_nonpos_iff_le a b)
  ... = (c - d ≤ 0) : by rewrite H
  ... ↔ c ≤ d       : sub_nonpos_iff_le c d

Definition lt_iff_lt_of_sub_eq_sub {a b c d : A} (H : a - b = c - d) : a < b ↔ c < d.
  calc
  a < b ↔ a - b < 0   : iff.symm (sub_neg_iff_lt a b)
  ... = (c - d < 0) : by rewrite H
  ... ↔ c < d       : sub_neg_iff_lt c d

Definition sub_le_sub_left {a b : A} (H : a ≤ b) (c : A) : c - b ≤ c - a.
  add_le_add_left (neg_le_neg H) c

Definition sub_le_sub_right {a b : A} (H : a ≤ b) (c : A) : a - c ≤ b - c . add_le_add_right H (-c)

Definition sub_le_sub {a b c d : A} (Hab : a ≤ b) (Hcd : c ≤ d) : a - d ≤ b - c.
  add_le_add Hab (neg_le_neg Hcd)

Definition sub_lt_sub_left {a b : A} (H : a < b) (c : A) : c - b < c - a.
  add_lt_add_left (neg_lt_neg H) c

Definition sub_lt_sub_right {a b : A} (H : a < b) (c : A) : a - c < b - c . add_lt_add_right H (-c)

Definition sub_lt_sub {a b c d : A} (Hab : a < b) (Hcd : c < d) : a - d < b - c.
  add_lt_add Hab (neg_lt_neg Hcd)

Definition sub_lt_sub_of_le_of_lt {a b c d : A} (Hab : a ≤ b) (Hcd : c < d) : a - d < b - c.
  add_lt_add_of_le_of_lt Hab (neg_lt_neg Hcd)

Definition sub_lt_sub_of_lt_of_le {a b c d : A} (Hab : a < b) (Hcd : c ≤ d) : a - d < b - c.
  add_lt_add_of_lt_of_le Hab (neg_le_neg Hcd)

Definition sub_le_self (a : A) {b : A} (H : b ≥ 0) : a - b ≤ a.
  calc
  a - b = a + -b : rfl
  ... ≤ a + 0  : add_le_add_left (neg_nonpos_of_nonneg H)
  ... = a      : by rewrite add_zero

Definition sub_lt_self (a : A) {b : A} (H : b > 0) : a - b < a.
  calc
  a - b = a + -b : rfl
  ... < a + 0  : add_lt_add_left (neg_neg_of_pos H)
  ... = a      : by rewrite add_zero

Definition add_le_add_three {a b c d e f : A} (H1 : a ≤ d) (H2 : b ≤ e) (H3 : c ≤ f) :
  a + b + c ≤ d + e + f.
Proof.
  apply le.trans,
  apply add_le_add,
  apply add_le_add,
  repeat assumption,
  apply le.refl
Defined.

Definition sub_le_of_nonneg {b : A} (H : b ≥ 0) : a - b ≤ a.
  add_le_of_le_of_nonpos (le.refl a) (neg_nonpos_of_nonneg H)

Definition sub_lt_of_pos {b : A} (H : b > 0) : a - b < a.
  add_lt_of_le_of_neg (le.refl a) (neg_neg_of_pos H)

Definition neg_add_neg_le_neg_of_pos {a : A} (H : a > 0) : -a + -a ≤ -a.
  !neg_add # neg_le_neg (le_add_of_nonneg_left (le_of_lt H))
Defined.

(* linear ordered group with decidable order *)

structure decidable_linear_ordered_mul_ab_group [class] (A : Type)
  extends ab_group A, decidable_linear_order A.
  (mul_le_mul_left : forall a b, le a b -> forall c, le (mul c a) (mul c b))
  (mul_lt_mul_left : forall a b, lt a b -> forall c, lt (mul c a) (mul c b))

Definition decidable_linear_ordered_ab_group [class] : Type -> Type.
decidable_linear_ordered_mul_ab_group

Definition add_ab_group_of_decidable_linear_ordered_ab_group [trans_instance] (A : Type)
  [H : decidable_linear_ordered_ab_group A] : add_ab_group A.
@decidable_linear_ordered_mul_ab_group.to_ab_group A H

Definition decidable_linear_order_of_decidable_linear_ordered_ab_group [reducible]
  [trans_instance] (A : Type) [H : decidable_linear_ordered_ab_group A] :
  decidable_linear_order A.
@decidable_linear_ordered_mul_ab_group.to_decidable_linear_order A H

Definition decidable_linear_ordered_mul_ab_group.to_ordered_mul_ab_group [reducible]
  [trans_instance] (A : Type) [s : decidable_linear_ordered_mul_ab_group A] :
  ordered_mul_ab_group A.
( ordered_mul_ab_group, s,
  le_of_lt . @le_of_lt A _,
  lt_of_le_of_lt . @lt_of_le_of_lt A _,
  lt_of_lt_of_le . @lt_of_lt_of_le A _ )

Definition decidable_linear_ordered_ab_group.to_ordered_ab_group [trans_instance]
  (A : Type) [s : decidable_linear_ordered_ab_group A] : ordered_ab_group A.
@decidable_linear_ordered_mul_ab_group.to_ordered_mul_ab_group A s

section
  variables [s : decidable_linear_ordered_ab_group A]
  variables {a b c d e : A}
  include s

  (* these can be generalized to a lattice ordered group *)

Definition min_add_add_left : min (a + b) (a + c) = a + min b c.
  inverse (eq_min
  (show a + min b c ≤ a + b, from add_le_add_left !min_le_left _)
  (show a + min b c ≤ a + c, from add_le_add_left !min_le_right _)
  (take d,
  assume H₁ : d ≤ a + b,
  assume H₂ : d ≤ a + c,
  have H : d - a ≤ min b c,
  from le_min (iff.mp !le_add_iff_sub_left_le H₁) (iff.mp !le_add_iff_sub_left_le H₂),
  show d ≤ a + min b c, from iff.mpr !le_add_iff_sub_left_le H))

Definition min_add_add_right : min (a + c) (b + c) = min a b + c.
  by rewrite [add.comm a c, add.comm b c, add.comm _ c]; apply min_add_add_left

Definition max_add_add_left : max (a + b) (a + c) = a + max b c.
  inverse (eq_max
  (add_le_add_left !le_max_left _)
  (add_le_add_left !le_max_right _)
  (fun d H₁ H₂ =>
  have H : max b c ≤ d - a,
  from max_le (iff.mp !add_le_iff_le_sub_left H₁) (iff.mp !add_le_iff_le_sub_left H₂),
  show a + max b c ≤ d, from iff.mpr !add_le_iff_le_sub_left H))

Definition max_add_add_right : max (a + c) (b + c) = max a b + c.
  by rewrite [add.comm a c, add.comm b c, add.comm _ c]; apply max_add_add_left

Definition max_neg_neg : max (-a) (-b) = - min a b .
  inverse (eq_max
  (show -a ≤ -(min a b), from neg_le_neg !min_le_left)
  (show -b ≤ -(min a b), from neg_le_neg !min_le_right)
  (take d,
  assume H₁ : -a ≤ d,
  assume H₂ : -b ≤ d,
  have H : -d ≤ min a b,
  from le_min (!iff.mp !neg_le_iff_neg_le H₁) (!iff.mp !neg_le_iff_neg_le H₂),
  show -(min a b) ≤ d, from !iff.mp !neg_le_iff_neg_le H))

Definition min_eq_neg_max_neg_neg : min a b = - max (-a) (-b).
  by rewrite [max_neg_neg, neg_neg]

Definition min_neg_neg : min (-a) (-b) = - max a b.
  by rewrite [min_eq_neg_max_neg_neg, *neg_neg]

Definition max_eq_neg_min_neg_neg : max a b = - min (-a) (-b).
  by rewrite [min_neg_neg, neg_neg]

  (* absolute value *)
  variables {a b c}

Definition abs (a : A) : A . max a (-a)

Definition abs_of_nonneg (H : a ≥ 0) : abs a = a.
  have H' : -a ≤ a, from le.trans (neg_nonpos_of_nonneg H) H,
  max_eq_left H'

Definition abs_of_pos (H : a > 0) : abs a = a.
  abs_of_nonneg (le_of_lt H)

Definition abs_of_nonpos (H : a ≤ 0) : abs a = -a.
  have H' : a ≤ -a, from le.trans H (neg_nonneg_of_nonpos H),
  max_eq_right H'

Definition abs_of_neg (H : a < 0) : abs a = -a . abs_of_nonpos (le_of_lt H)

Definition abs_zero : abs 0 = (0:A) . abs_of_nonneg (le.refl _)

Definition abs_neg (a : A) : abs (-a) = abs a.
  by rewrite [↑abs, max.comm, neg_neg]

Definition abs_pos_of_pos (H : a > 0) : abs a > 0.
  by rewrite (abs_of_pos H); exact H

Definition abs_pos_of_neg (H : a < 0) : abs a > 0.
  !abs_neg # abs_pos_of_pos (neg_pos_of_neg H)

Definition abs_sub (a b : A) : abs (a - b) = abs (b - a).
  by rewrite [-neg_sub, abs_neg]

Definition ne_zero_of_abs_ne_zero {a : A} (H : abs a ≠ 0) : a ≠ 0.
  assume Ha, H (Ha^-1 # abs_zero)

  (* these assume a linear order *)

Definition eq_zero_of_neg_eq (H : -a = a) : a = 0.
  lt.by_cases
  (assume H1 : a < 0,
  have H2: a > 0, from H # neg_pos_of_neg H1,
  absurd H1 (lt.asymm H2))
  (assume H1 : a = 0, H1)
  (assume H1 : a > 0,
  have H2: a < 0, from H # neg_neg_of_pos H1,
  absurd H1 (lt.asymm H2))

Definition abs_nonneg (a : A) : abs a ≥ 0.
  sum.elim (le.total 0 a)
  (assume H : 0 ≤ a, by rewrite (abs_of_nonneg H); exact H)
  (assume H : a ≤ 0,
  calc
  0 ≤ -a    : neg_nonneg_of_nonpos H
  ... = abs a : abs_of_nonpos H)

Definition abs_abs (a : A) : abs (abs a) = abs a . abs_of_nonneg !abs_nonneg

Definition le_abs_self (a : A) : a ≤ abs a.
  sum.elim (le.total 0 a)
  (assume H : 0 ≤ a, abs_of_nonneg H # !le.refl)
  (assume H : a ≤ 0, le.trans H !abs_nonneg)

Definition neg_le_abs_self (a : A) : -a ≤ abs a.
  !abs_neg # !le_abs_self

Definition eq_zero_of_abs_eq_zero (H : abs a = 0) : a = 0.
  have H1 : a ≤ 0, from H # le_abs_self a,
  have H2 : -a ≤ 0, from H # abs_neg a # le_abs_self (-a),
  le.antisymm H1 (nonneg_of_neg_nonpos H2)

Definition abs_eq_zero_iff_eq_zero (a : A) : abs a = 0 ↔ a = 0.
  iff.intro eq_zero_of_abs_eq_zero (assume H, ap abs H @ !abs_zero)

Definition eq_of_abs_sub_eq_zero {a b : A} (H : abs (a - b) = 0) : a = b.
  have a - b = 0, from eq_zero_of_abs_eq_zero H,
  show a = b, from eq_of_sub_eq_zero this

Definition abs_pos_of_ne_zero (H : a ≠ 0) : abs a > 0.
  sum.elim (lt_sum_gt_of_ne H) abs_pos_of_neg abs_pos_of_pos

Definition abs.by_cases {P : A -> Type} {a : A} (H1 : P a) (H2 : P (-a)) : P (abs a).
  sum.elim (le.total 0 a)
  (assume H : 0 ≤ a, (abs_of_nonneg H)^-1 # H1)
  (assume H : a ≤ 0, (abs_of_nonpos H)^-1 # H2)

Definition abs_le_of_le_of_neg_le (H1 : a ≤ b) (H2 : -a ≤ b) : abs a ≤ b.
  abs.by_cases H1 H2

Definition abs_lt_of_lt_of_neg_lt (H1 : a < b) (H2 : -a < b) : abs a < b.
  abs.by_cases H1 H2

  (* the triangle inequality *)
  section
  private lemma aux1 {a b : A} (H1 : a + b ≥ 0) (H2 : a ≥ 0) : abs (a + b) ≤ abs a + abs b.
  decidable.by_cases
  (assume H3 : b ≥ 0,
  calc
  abs (a + b) ≤ abs (a + b)   : le.refl
  ... = a + b             : by rewrite (abs_of_nonneg H1)
  ... = abs a + b         : by rewrite (abs_of_nonneg H2)
  ... = abs a + abs b     : by rewrite (abs_of_nonneg H3))
  (assume H3 : ¬ b ≥ 0,
  have H4 : b ≤ 0, from le_of_lt (lt_of_not_ge H3),
  calc
  abs (a + b) = a + b     : by rewrite (abs_of_nonneg H1)
  ... = abs a + b     : by rewrite (abs_of_nonneg H2)
  ... ≤ abs a + 0     : add_le_add_left H4
  ... ≤ abs a + -b    : add_le_add_left (neg_nonneg_of_nonpos H4)
  ... = abs a + abs b : by rewrite (abs_of_nonpos H4))

  private lemma aux2 {a b : A} (H1 : a + b ≥ 0) : abs (a + b) ≤ abs a + abs b.
  sum.elim (le.total b 0)
  (assume H2 : b ≤ 0,
  have H3 : ¬ a < 0, from
  assume H4 : a < 0,
  have H5 : a + b < 0, from !add_zero # add_lt_add_of_lt_of_le H4 H2,
  not_lt_of_ge H1 H5,
  aux1 H1 (le_of_not_gt H3))
  (assume H2 : 0 ≤ b,
Proof.
  have H3 : abs (b + a) ≤ abs b + abs a,
Proof.
  rewrite add.comm at H1,
  exact aux1 H1 H2
Defined.,
  rewrite [add.comm, {abs a + _}add.comm],
  exact H3
Defined.)

Definition abs_add_le_abs_add_abs (a b : A) : abs (a + b) ≤ abs a + abs b.
  sum.elim (le.total 0 (a + b))
  (assume H2 : 0 ≤ a + b, aux2 H2)
  (assume H2 : a + b ≤ 0,
  have H3 : -a + -b = -(a + b), by rewrite neg_add,
  have H4 : -(a + b) ≥ 0, from iff.mpr (neg_nonneg_iff_nonpos (a+b)) H2,
  have H5   : -a + -b ≥ 0, begin rewrite -H3 at H4, exact H4 end,
  calc
  abs (a + b) = abs (-a + -b)   : by rewrite [-abs_neg, neg_add]
  ... ≤ abs (-a) + abs (-b) : aux2 H5
  ... = abs a + abs b       : by rewrite *abs_neg)

Definition abs_sub_abs_le_abs_sub (a b : A) : abs a - abs b ≤ abs (a - b).
  have H1 : abs a - abs b + abs b ≤ abs (a - b) + abs b, from
  calc
  abs a - abs b + abs b = abs a : by rewrite sub_add_cancel
  ... = abs (a - b + b)       : by rewrite sub_add_cancel
  ... ≤ abs (a - b) + abs b   : abs_add_le_abs_add_abs,
  le_of_add_le_add_right H1

Definition abs_sub_le (a b c : A) : abs (a - c) ≤ abs (a - b) + abs (b - c).
  calc
  abs (a - c) = abs (a - b + (b - c)) :  by rewrite [*sub_eq_add_neg, add.assoc, neg_add_cancel_left]
  ... ≤ abs (a - b) + abs (b - c) : abs_add_le_abs_add_abs

Definition abs_add_three (a b c : A) : abs (a + b + c) ≤ abs a + abs b + abs c.
Proof.
  apply le.trans,
  apply abs_add_le_abs_add_abs,
  apply le.trans,
  apply add_le_add_right,
  apply abs_add_le_abs_add_abs,
  apply le.refl
Defined.

Definition dist_bdd_within_interval {a b lb ub : A} (H : lb < ub) (Hal : lb ≤ a) (Hau : a ≤ ub)
  (Hbl : lb ≤ b) (Hbu : b ≤ ub) : abs (a - b) ≤ ub - lb.
Proof.
  cases (decidable.em (b ≤ a)) with [Hba, Hba],
  rewrite (abs_of_nonneg (iff.mpr !sub_nonneg_iff_le Hba)),
  apply sub_le_sub,
  apply Hau,
  apply Hbl,
  rewrite [abs_of_neg (iff.mpr !sub_neg_iff_lt (lt_of_not_ge Hba)), neg_sub],
  apply sub_le_sub,
  apply Hbu,
  apply Hal
Defined.

Defined.
Defined.

Defined. algebra
