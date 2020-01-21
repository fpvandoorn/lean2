(*
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Structures with multiplicative and additive components, including semirings, rings, and fields.
The development is modeled after Isabelle's library.
*)

import algebra.group
open eq eq.ops algebra
set_option class.force_new true

variable {A : Type}
namespace algebra
(* auxiliary classes *)

structure distrib [class] (A : Type) extends has_mul A, has_add A.
(left_distrib : forall a b c, mul a (add b c) = add (mul a b) (mul a c))
(right_distrib : forall a b c, mul (add a b) c = add (mul a c) (mul b c))

Definition left_distrib [s : distrib A] (a b c : A) : a * (b + c) = a * b + a * c.
!distrib.left_distrib

Definition right_distrib [s: distrib A] (a b c : A) : (a + b) * c = a * c + b * c.
!distrib.right_distrib

structure mul_zero_class [class] (A : Type) extends has_mul A, has_zero A.
(zero_mul : forall a, mul zero a = zero)
(mul_zero : forall a, mul a zero = zero)

Definition zero_mul [s : mul_zero_class A] (a : A) : 0 * a = 0 . !mul_zero_class.zero_mul
Definition mul_zero [s : mul_zero_class A] (a : A) : a * 0 = 0 . !mul_zero_class.mul_zero

structure zero_ne_one_class [class] (A : Type) extends has_zero A, has_one A.
(zero_ne_one : zero ≠ one)

Definition zero_ne_one [s: zero_ne_one_class A] : 0 ≠ (1:A) . @zero_ne_one_class.zero_ne_one A s

(* semiring *)
structure semiring (A : Type) extends comm_monoid A renaming
  mul->add mul_assoc->add_assoc one->zero one_mul->zero_add mul_one->add_zero mul_comm->add_comm,
  monoid A, distrib A, mul_zero_class A

(* we make it a class now (and not as part of the structure) to avoid
  semiring.to_comm_monoid to be an instance *)


Definition add_comm_monoid_of_semiring [trans_instance] (A : Type)
  [H : semiring A] : add_comm_monoid A.
@semiring.to_comm_monoid A H

Definition monoid_of_semiring [trans_instance] (A : Type)
  [H : semiring A] : monoid A.
@semiring.to_monoid A H

Definition distrib_of_semiring [trans_instance] (A : Type)
  [H : semiring A] : distrib A.
@semiring.to_distrib A H

Definition mul_zero_class_of_semiring [trans_instance] (A : Type)
  [H : semiring A] : mul_zero_class A.
@semiring.to_mul_zero_class A H

section semiring
  variables [s : semiring A] (a b c : A)
  include s

Definition As {a b c : A} : a + b + c = a + (b + c).
  !add.assoc

Definition one_add_one_eq_two : 1 + 1 = 2 :> A.
  by unfold bit0

Definition ne_zero_of_mul_ne_zero_right {a b : A} (H : a * b ≠ 0) : a ≠ 0.
  suppose a = 0,
  have a * b = 0, from this^-1 # zero_mul b,
  H this

Definition ne_zero_of_mul_ne_zero_left {a b : A} (H : a * b ≠ 0) : b ≠ 0.
  suppose b = 0,
  have a * b = 0, from this^-1 # mul_zero a,
  H this

Definition distrib_three_right (a b c d : A) : (a + b + c) * d = a * d + b * d + c * d.
  by rewrite *right_distrib

Definition mul_two : a * 2 = a + a.
  by rewrite [-one_add_one_eq_two, left_distrib, +mul_one]

Definition two_mul : 2 * a = a + a.
  by rewrite [-one_add_one_eq_two, right_distrib, +one_mul]

Defined. semiring

(* comm semiring *)

structure comm_semiring [class] (A : Type) extends semiring A, comm_monoid A
(* TODO: we could also define a cancelative comm_semiring, i.e. satisfying *)
(* c ≠ 0 -> c * a = c * b -> a = b. *)

section comm_semiring
  variables [s : comm_semiring A] (a b c : A)
  include s

  protectedDefinition algebra.dvd (a b : A) : Type . Σc, b = a * c

Definition comm_semiring_has_dvd [instance] [priority algebra.prio] : has_dvd A.
  has_dvd.mk algebra.dvd

Definition dvd.intro {a b c : A} (H : a * c = b) : a ∣ b.
  sigma.mk _ H^-1

Definition dvd_of_mul_right_eq {a b c : A} (H : a * c = b) : a ∣ b . dvd.intro H

Definition dvd.intro_left {a b c : A} (H : c * a = b) : a ∣ b.
  dvd.intro (!mul.comm # H)

Definition dvd_of_mul_left_eq {a b c : A} (H : c * a = b) : a ∣ b . dvd.intro_left H

Definition exists_eq_mul_right_of_dvd {a b : A} (H : a ∣ b) : Σc, b = a * c . H

Definition dvd.elim {P : Type} {a b : A} (H₁ : a ∣ b) (H₂ : forall c, b = a * c -> P) : P.
  sigma.rec_on H₁ H₂

Definition exists_eq_mul_left_of_dvd {a b : A} (H : a ∣ b) : Σc, b = c * a.
  dvd.elim H (take c, assume H1 : b = a * c, sigma.mk c (H1 @ !mul.comm))

Definition dvd.elim_left {P : Type} {a b : A} (H₁ : a ∣ b) (H₂ : forall c, b = c * a -> P) : P.
  sigma.rec_on (exists_eq_mul_left_of_dvd H₁) (take c, assume H₃ : b = c * a, H₂ c H₃)

Definition dvd.refl : a ∣ a . dvd.intro !mul_one

Definition dvd.trans {a b c : A} (H₁ : a ∣ b) (H₂ : b ∣ c) : a ∣ c.
  dvd.elim H₁
  (take d, assume H₃ : b = a * d,
  dvd.elim H₂
  (take e, assume H₄ : c = b * e,
  dvd.intro
  (show a * (d * e) = c, by rewrite [-mul.assoc, -H₃, H₄])))

Definition eq_zero_of_zero_dvd {a : A} (H : 0 ∣ a) : a = 0.
  dvd.elim H (take c, assume H' : a = 0 * c, H' @ !zero_mul)

Definition dvd_zero : a ∣ 0 . dvd.intro !mul_zero

Definition one_dvd : 1 ∣ a . dvd.intro !one_mul

Definition dvd_mul_right : a ∣ a * b . dvd.intro rfl

Definition dvd_mul_left : a ∣ b * a . mul.comm a b # dvd_mul_right a b

Definition dvd_mul_of_dvd_left {a b : A} (H : a ∣ b) (c : A) : a ∣ b * c.
  dvd.elim H
  (take d,
  suppose b = a * d,
  dvd.intro
  (show a * (d * c) = b * c, from by rewrite [-mul.assoc]; substvars))

Definition dvd_mul_of_dvd_right {a b : A} (H : a ∣ b) (c : A) : a ∣ c * b.
  !mul.comm # (dvd_mul_of_dvd_left H _)

Definition mul_dvd_mul {a b c d : A} (dvd_ab : a ∣ b) (dvd_cd : c ∣ d) : a * c ∣ b * d.
  dvd.elim dvd_ab
  (take e, suppose b = a * e,
  dvd.elim dvd_cd
  (take f, suppose d = c * f,
  dvd.intro
  (show a * c * (e * f) = b * d,
  by rewrite [mul.assoc, {c*_}mul.left_comm, -mul.assoc]; substvars)))

Definition dvd_of_mul_right_dvd {a b c : A} (H : a * b ∣ c) : a ∣ c.
  dvd.elim H (take d, assume Habdc : c = a * b * d, dvd.intro (!mul.assoc^-1 @ Habdc^-1))

Definition dvd_of_mul_left_dvd {a b c : A} (H : a * b ∣ c) : b ∣ c.
  dvd_of_mul_right_dvd (mul.comm a b # H)

Definition dvd_add {a b c : A} (Hab : a ∣ b) (Hac : a ∣ c) : a ∣ b + c.
  dvd.elim Hab
  (take d, suppose b = a * d,
  dvd.elim Hac
  (take e, suppose c = a * e,
  dvd.intro (show a * (d + e) = b + c,
  by rewrite [left_distrib]; substvars)))
Defined. comm_semiring

(* ring *)

structure ring (A : Type) extends ab_group A renaming mul->add mul_assoc->add_assoc
  one->zero one_mul->zero_add mul_one->add_zero inv->neg mul_left_inv->add_left_inv mul_comm->add_comm,
  monoid A, distrib A

(* we make it a class now (and not as part of the structure) to avoid
  ring.to_ab_group to be an instance *)


Definition add_ab_group_of_ring [trans_instance] (A : Type)
  [H : ring A] : add_ab_group A.
@ring.to_ab_group A H

Definition monoid_of_ring [trans_instance] (A : Type)
  [H : ring A] : monoid A.
@ring.to_monoid A H

Definition distrib_of_ring [trans_instance] (A : Type)
  [H : ring A] : distrib A.
@ring.to_distrib A H

Definition ring.mul_zero [s : ring A] (a : A) : a * 0 = 0.
have a * 0 + 0 = a * 0 + a * 0, from calc
  a * 0 + 0 = a * 0         : by rewrite add_zero
  ... = a * (0 + 0)   : by rewrite add_zero
  ... = a * 0 + a * 0 : by rewrite {a*_}ring.left_distrib,
show a * 0 = 0, from (add.left_cancel this)^-1

Definition ring.zero_mul [s : ring A] (a : A) : 0 * a = 0.
have 0 * a + 0 = 0 * a + 0 * a, from calc
  0 * a + 0 = 0 * a         : by rewrite add_zero
  ... = (0 + 0) * a   : by rewrite add_zero
  ... = 0 * a + 0 * a : by rewrite {_*a}ring.right_distrib,
show 0 * a = 0, from  (add.left_cancel this)^-1

Definition ring.to_semiring [trans_instance] [s : ring A] : semiring A.
( semiring, s,
  mul_zero . ring.mul_zero,
  zero_mul . ring.zero_mul )

section
  variables [s : ring A] (a b c d e : A)
  include s

Definition neg_mul_eq_neg_mul : -(a * b) = -a * b.
  neg_eq_of_add_eq_zero
Proof.
  rewrite [-right_distrib, add.right_inv, zero_mul]
Defined.

Definition neg_mul_eq_mul_neg : -(a * b) = a * -b.
  neg_eq_of_add_eq_zero
Proof.
  rewrite [-left_distrib, add.right_inv, mul_zero]
Defined.

Definition neg_mul_eq_neg_mul_symm : - a * b = - (a * b) . inverse !neg_mul_eq_neg_mul
Definition mul_neg_eq_neg_mul_symm : a * - b = - (a * b) . inverse !neg_mul_eq_mul_neg

Definition neg_mul_neg : -a * -b = a * b.
  calc
  -a * -b = -(a * -b) : by rewrite -neg_mul_eq_neg_mul
  ... = - -(a * b)  : by rewrite -neg_mul_eq_mul_neg
  ... = a * b       : by rewrite neg_neg

Definition neg_mul_comm : -a * b = a * -b . !neg_mul_eq_neg_mul^-1 @ !neg_mul_eq_mul_neg

Definition neg_eq_neg_one_mul : -a = -1 * a.
  calc
  -a = -(1 * a)  : by rewrite one_mul
  ... = -1 * a : by rewrite neg_mul_eq_neg_mul

Definition mul_sub_left_distrib : a * (b - c) = a * b - a * c.
  calc
  a * (b - c) = a * b + a * -c : left_distrib
  ... = a * b + - (a * c)    : by rewrite -neg_mul_eq_mul_neg
  ... = a * b - a * c        : rfl

Definition mul_sub_right_distrib : (a - b) * c = a * c - b * c.
  calc
  (a - b) * c = a * c  + -b * c : right_distrib
  ... = a * c + - (b * c)     : by rewrite neg_mul_eq_neg_mul
  ... = a * c - b * c         : rfl

  (* TODO: can calc mode be improved to make this easier? *)
  (* TODO: there is also the other direction. It will be easier when we *)
  (* have the simplifier. *)

Definition mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d.
  calc
  a * e + c = b * e + d ↔ a * e + c = d + b * e : by rewrite {b*e+_}add.comm
  ... ↔ a * e + c - b * e = d : iff.symm !sub_eq_iff_eq_add
  ... ↔ a * e - b * e + c = d : by rewrite sub_add_eq_add_sub
  ... ↔ (a - b) * e + c = d   : by rewrite mul_sub_right_distrib

Definition mul_add_eq_mul_add_of_sub_mul_add_eq : (a - b) * e + c = d -> a * e + c = b * e + d.
  iff.mpr !mul_add_eq_mul_add_iff_sub_mul_add_eq

Definition sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d -> (a - b) * e + c = d.
  iff.mp !mul_add_eq_mul_add_iff_sub_mul_add_eq

Definition mul_neg_one_eq_neg : a * (-1) = -a.
  have a + a * -1 = 0, from calc
  a + a * -1 = a * 1 + a * -1 : mul_one
  ... = a * (1 + -1)   : left_distrib
  ... = a * 0          : by rewrite add.right_inv
  ... = 0              : mul_zero,
  symm (neg_eq_of_add_eq_zero this)

Definition ne_zero_prod_ne_zero_of_mul_ne_zero {a b : A} (H : a * b ≠ 0) : a ≠ 0 \* b ≠ 0.
  have a ≠ 0, from
  (suppose a = 0,
  have a * b = 0, by rewrite [this, zero_mul],
  absurd this H),
  have b ≠ 0, from
  (suppose b = 0,
  have a * b = 0, by rewrite [this, mul_zero],
  absurd this H),
  prod.mk `a ≠ 0` `b ≠ 0`
Defined.

structure comm_ring [class] (A : Type) extends ring A, comm_semigroup A

Definition comm_ring.to_comm_semiring [trans_instance] [s : comm_ring A] :
  comm_semiring A.
( comm_semiring, s,
  mul_zero . mul_zero,
  zero_mul . zero_mul )

section
  variables [s : comm_ring A] (a b c d e : A)
  include s

Definition mul_self_sub_mul_self_eq : a * a - b * b = (a + b) * (a - b).
Proof.
  krewrite [left_distrib, *right_distrib, add.assoc],
  rewrite [-{b*a + _}add.assoc,
  -*neg_mul_eq_mul_neg, {a*b}mul.comm, add.right_inv, zero_add]
Defined.

Definition mul_self_sub_one_eq : a * a - 1 = (a + 1) * (a - 1).
  by rewrite [-mul_self_sub_mul_self_eq, mul_one]

Definition dvd_neg_iff_dvd : (a ∣ -b) ↔ (a ∣ b).
  iff.intro
  (suppose a ∣ -b,
  dvd.elim this
  (take c, suppose -b = a * c,
  dvd.intro
  (show a * -c = b,
  by rewrite [-neg_mul_eq_mul_neg, -this, neg_neg])))
  (suppose a ∣ b,
  dvd.elim this
  (take c, suppose b = a * c,
  dvd.intro
  (show a * -c = -b,
  by rewrite [-neg_mul_eq_mul_neg, -this])))

Definition dvd_neg_of_dvd : (a ∣ b) -> (a ∣ -b).
  iff.mpr !dvd_neg_iff_dvd

Definition dvd_of_dvd_neg : (a ∣ -b) -> (a ∣ b).
  iff.mp !dvd_neg_iff_dvd

Definition neg_dvd_iff_dvd : (-a ∣ b) ↔ (a ∣ b).
  iff.intro
  (suppose -a ∣ b,
  dvd.elim this
  (take c, suppose b = -a * c,
  dvd.intro
  (show a * -c = b, by rewrite [-neg_mul_comm, this])))
  (suppose a ∣ b,
  dvd.elim this
  (take c, suppose b = a * c,
  dvd.intro
  (show -a * -c = b, by rewrite [neg_mul_neg, this])))

Definition neg_dvd_of_dvd : (a ∣ b) -> (-a ∣ b).
  iff.mpr !neg_dvd_iff_dvd

Definition dvd_of_neg_dvd : (-a ∣ b) -> (a ∣ b).
  iff.mp !neg_dvd_iff_dvd

Definition dvd_sub (H₁ : (a ∣ b)) (H₂ : (a ∣ c)) : (a ∣ b - c).
  dvd_add H₁ (!dvd_neg_of_dvd H₂)
Defined.

(* integral domains *)

structure no_zero_divisors [class] (A : Type) extends has_mul A, has_zero A.
(eq_zero_sum_eq_zero_of_mul_eq_zero : forall a b, mul a b = zero -> a = zero ⊎ b = zero)

Definition eq_zero_sum_eq_zero_of_mul_eq_zero {A : Type} [s : no_zero_divisors A] {a b : A}
  (H : a * b = 0) :
  a = 0 ⊎ b = 0 . !no_zero_divisors.eq_zero_sum_eq_zero_of_mul_eq_zero H

structure integral_domain [class] (A : Type) extends comm_ring A, no_zero_divisors A,
  zero_ne_one_class A

section
  variables [s : integral_domain A] (a b c d e : A)
  include s

Definition mul_ne_zero {a b : A} (H1 : a ≠ 0) (H2 : b ≠ 0) : a * b ≠ 0.
  suppose a * b = 0,
  sum.elim (eq_zero_sum_eq_zero_of_mul_eq_zero this) (assume H3, H1 H3) (assume H4, H2 H4)

Definition eq_of_mul_eq_mul_right {a b c : A} (Ha : a ≠ 0) (H : b * a = c * a) : b = c.
  have b * a - c * a = 0, from iff.mp !eq_iff_sub_eq_zero H,
  have (b - c) * a = 0, by rewrite [mul_sub_right_distrib, this],
  have b - c = 0, from sum_resolve_left (eq_zero_sum_eq_zero_of_mul_eq_zero this) Ha,
  iff.elim_right !eq_iff_sub_eq_zero this

Definition eq_of_mul_eq_mul_left {a b c : A} (Ha : a ≠ 0) (H : a * b = a * c) : b = c.
  have a * b - a * c = 0, from iff.mp !eq_iff_sub_eq_zero H,
  have a * (b - c) = 0, by rewrite [mul_sub_left_distrib, this],
  have b - c = 0, from sum_resolve_right (eq_zero_sum_eq_zero_of_mul_eq_zero this) Ha,
  iff.elim_right !eq_iff_sub_eq_zero this

  (* TODO: do we want the iff versions? *)

Definition eq_zero_of_mul_eq_self_right {a b : A} (H₁ : b ≠ 1) (H₂ : a * b = a) : a = 0.
  have b - 1 ≠ 0, from
  suppose b - 1 = 0, H₁ (!zero_add # eq_add_of_sub_eq this),
  have a * b - a = 0, by rewrite H₂; apply sub_self,
  have a * (b - 1) = 0, by rewrite [mul_sub_left_distrib, mul_one]; apply this,
  show a = 0, from sum_resolve_left (eq_zero_sum_eq_zero_of_mul_eq_zero this) `b - 1 ≠ 0`

Definition eq_zero_of_mul_eq_self_left {a b : A} (H₁ : b ≠ 1) (H₂ : b * a = a) : a = 0.
  eq_zero_of_mul_eq_self_right H₁ (!mul.comm # H₂)

Definition mul_self_eq_mul_self_iff (a b : A) : a * a = b * b ↔ a = b ⊎ a = -b.
  iff.intro
  (suppose a * a = b * b,
  have (a - b) * (a + b) = 0,
  by rewrite [mul.comm, -mul_self_sub_mul_self_eq, this, sub_self],
  have a - b = 0 ⊎ a + b = 0, from !eq_zero_sum_eq_zero_of_mul_eq_zero this,
  sum.elim this
  (suppose a - b = 0, sum.inl (eq_of_sub_eq_zero this))
  (suppose a + b = 0, sum.inr (eq_neg_of_add_eq_zero this)))
  (suppose a = b ⊎ a = -b, sum.elim this
  (suppose a = b,  by rewrite this)
  (suppose a = -b, by rewrite [this, neg_mul_neg]))

Definition mul_self_eq_one_iff (a : A) : a * a = 1 ↔ a = 1 ⊎ a = -1.
  have a * a = 1 * 1 ↔ a = 1 ⊎ a = -1, from mul_self_eq_mul_self_iff a 1,
  by rewrite mul_one at this; exact this

  (* TODO: c - b * c -> c = 0 ⊎ b = 1 and variants *)

Definition dvd_of_mul_dvd_mul_left {a b c : A} (Ha : a ≠ 0) (Hdvd : (a * b ∣ a * c)) : (b ∣ c).
  dvd.elim Hdvd
  (take d,
  suppose a * c = a * b * d,
  have b * d = c, from eq_of_mul_eq_mul_left Ha (mul.assoc a b d # this^-1),
  dvd.intro this)

Definition dvd_of_mul_dvd_mul_right {a b c : A} (Ha : a ≠ 0) (Hdvd : (b * a ∣ c * a)) : (b ∣ c).
  dvd.elim Hdvd
  (take d,
  suppose c * a = b * a * d,
  have b * d * a = c * a, from by rewrite [mul.right_comm, -this],
  have b * d = c, from eq_of_mul_eq_mul_right Ha this,
  dvd.intro this)
Defined.

namespace norm_num

Definition mul_zero [s : mul_zero_class A] (a : A) : a * zero = zero.
  by rewrite [↑zero, mul_zero]

Definition zero_mul [s : mul_zero_class A] (a : A) : zero * a = zero.
  by rewrite [↑zero, zero_mul]

Definition mul_one [s : monoid A] (a : A) : a * one = a.
  by rewrite [↑one, mul_one]

Definition mul_bit0 [s : distrib A] (a b : A) : a * (bit0 b) = bit0 (a * b).
  by rewrite [↑bit0, left_distrib]

Definition mul_bit0_helper [s : distrib A] (a b t : A) (H : a * b = t) : a * (bit0 b) = bit0 t.
  by rewrite -H; apply mul_bit0

Definition mul_bit1 [s : semiring A] (a b : A) : a * (bit1 b) = bit0 (a * b) + a.
  by rewrite [↑bit1, ↑bit0, +left_distrib, ↑one, mul_one]

Definition mul_bit1_helper [s : semiring A] (a b s t : A) (Hs : a * b = s) (Ht : bit0 s + a  = t) :
  a * (bit1 b) = t.
Proof. rewrite [-Ht, -Hs, mul_bit1] end

Definition subst_into_prod [s : has_mul A] (l r tl tr t : A) (prl : l = tl) (prr : r = tr)
  (prt : tl * tr = t) :
  l * r = t.
  by rewrite [prl, prr, prt]

Definition mk_cong (op : A -> A) (a b : A) (H : a = b) : op a = op b.
  by congruence; exact H

Definition mk_eq (a : A) : a = a . rfl

Definition neg_add_neg_eq_of_add_add_eq_zero [s : add_ab_group A] (a b c : A) (H : c + a + b = 0) :
  -a + -b = c.
Proof.
  apply add_neg_eq_of_eq_add,
  apply neg_eq_of_add_eq_zero,
  rewrite [add.comm, add.assoc, add.comm b, -add.assoc, H]
Defined.

Definition neg_add_neg_helper [s : add_ab_group A] (a b c : A) (H : a + b = c) : -a + -b = -c.
Proof. apply iff.mp !neg_eq_neg_iff_eq, rewrite [neg_add, *neg_neg, H] end

Definition neg_add_pos_eq_of_eq_add [s : add_ab_group A] (a b c : A) (H : b = c + a) : -a + b = c.
Proof. apply neg_add_eq_of_eq_add, rewrite add.comm, exact H end

Definition neg_add_pos_helper1 [s : add_ab_group A] (a b c : A) (H : b + c = a) : -a + b = -c.
Proof. apply neg_add_eq_of_eq_add, apply eq_add_neg_of_add_eq H end

Definition neg_add_pos_helper2 [s : add_ab_group A] (a b c : A) (H : a + c = b) : -a + b = c.
Proof. apply neg_add_eq_of_eq_add, rewrite H end

Definition pos_add_neg_helper [s : add_ab_group A] (a b c : A) (H : b + a = c) : a + b = c.
  by rewrite [add.comm, H]

Definition sub_eq_add_neg_helper [s : add_ab_group A] (t₁ t₂ e w₁ w₂: A) (H₁ : t₁ = w₁)
  (H₂ : t₂ = w₂) (H : w₁ + -w₂ = e) : t₁ - t₂ = e.
  by rewrite [sub_eq_add_neg, H₁, H₂, H]

Definition pos_add_pos_helper [s : add_ab_group A] (a b c h₁ h₂ : A) (H₁ : a = h₁) (H₂ : b = h₂)
  (H : h₁ + h₂ = c) : a + b = c.
  by rewrite [H₁, H₂, H]

Definition subst_into_subtr [s : add_group A] (l r t : A) (prt : l + -r = t) : l - r = t.
  by rewrite [sub_eq_add_neg, prt]

Definition neg_neg_helper [s : add_group A] (a b : A) (H : a = -b) : -a = b.
  by rewrite [H, neg_neg]

Definition neg_mul_neg_helper [s : ring A] (a b c : A) (H : a * b = c) : (-a) * (-b) = c.
Proof. rewrite [neg_mul_neg, H] end

Definition neg_mul_pos_helper [s : ring A] (a b c : A) (H : a * b = c) : (-a) * b = -c.
Proof. rewrite [-neg_mul_eq_neg_mul, H] end

Definition pos_mul_neg_helper [s : ring A] (a b c : A) (H : a * b = c) : a * (-b) = -c.
Proof. rewrite [-neg_mul_comm, -neg_mul_eq_neg_mul, H] end

Defined. norm_num
Defined. algebra
open algebra


  zero_mul mul_zero
  at simplifier.unit


  neg_mul_eq_neg_mul_symm mul_neg_eq_neg_mul_symm
  at simplifier.neg


  left_distrib right_distrib
  at simplifier.distrib
