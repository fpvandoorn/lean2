(*
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Weak orders "≤", strict orders "<", and structures that include both.
*)
import algebra.binary
open eq eq.ops algebra
(* set_option class.force_new true *)

variable {A : Type}

(* weak orders *)

namespace algebra
structure weak_order [class] (A : Type) extends has_le A.
(le_refl : forall a, le a a)
(le_trans : forall a b c, le a b -> le b c -> le a c)
(le_antisymm : forall a b, le a b -> le b a -> a = b)

section
  variable [s : weak_order A]
  include s

Definition le.refl [refl] (a : A) : a ≤ a . !weak_order.le_refl

Definition le_of_eq {a b : A} (H : a = b) : a ≤ b . H # le.refl a

Definition le.trans [trans] {a b c : A} : a ≤ b -> b ≤ c -> a ≤ c . !weak_order.le_trans

Definition ge.trans [trans] {a b c : A} (H1 : a ≥ b) (H2: b ≥ c) : a ≥ c . le.trans H2 H1

Definition le.antisymm {a b : A} : a ≤ b -> b ≤ a -> a = b . !weak_order.le_antisymm

  (* Alternate syntax. (Abbreviations do not migrate well.) *)
Definition eq_of_le_of_ge {a b : A} : a ≤ b -> b ≤ a -> a = b . !le.antisymm
Defined.

structure linear_weak_order [class] (A : Type) extends weak_order A.
(le_total : forall a b, le a b ⊎ le b a)

section
  variables [linear_weak_order A]

Definition le.total (a b : A) : a ≤ b ⊎ b ≤ a . !linear_weak_order.le_total

Definition le_of_not_ge {a b : A} (H : ¬ a ≥ b) : a ≤ b . sum.resolve_left !le.total H

Definition le_by_cases (a b : A) {P : Type} (H1 : a ≤ b -> P) (H2 : b ≤ a -> P) : P.
Proof.
  cases (le.total a b) with H H,
  { exact H1 H},
  { exact H2 H}
Defined.
Defined.

(* strict orders *)

structure strict_order [class] (A : Type) extends has_lt A.
(lt_irrefl : forall a, ¬ lt a a)
(lt_trans : forall a b c, lt a b -> lt b c -> lt a c)

section
  variable [s : strict_order A]
  include s

Definition lt.irrefl (a : A) : ¬ a < a . !strict_order.lt_irrefl
Definition not_lt_self (a : A) : ¬ a < a . !lt.irrefl   (* alternate syntax *)

Definition lt_self_iff_empty (a : A) : a < a ↔ empty.
  iff_empty_intro (lt.irrefl a)

Definition lt.trans [trans] {a b c : A} : a < b -> b < c -> a < c . !strict_order.lt_trans

Definition gt.trans [trans] {a b c : A} (H1 : a > b) (H2: b > c) : a > c . lt.trans H2 H1

Definition ne_of_lt {a b : A} (lt_ab : a < b) : a ≠ b.
  assume eq_ab : a = b,
  show empty, from lt.irrefl b (eq_ab # lt_ab)

Definition ne_of_gt {a b : A} (gt_ab : a > b) : a ≠ b.
  ne.symm (ne_of_lt gt_ab)

Definition lt.asymm {a b : A} (H : a < b) : ¬ b < a.
  assume H1 : b < a, lt.irrefl _ (lt.trans H H1)

Definition not_lt_of_gt {a b : A} (H : a > b) : ¬ a < b . !lt.asymm H    (* alternate syntax *)
Defined.

(* well-founded orders *)

structure wf_strict_order [class] (A : Type) extends strict_order A.
(wf_rec : forall P : A -> Type, (forall x, (forall y, lt y x -> P y) -> P x) -> forall x, P x)

Definition wf.rec_on {A : Type} [s : wf_strict_order A] {P : A -> Type}
  (x : A) (H : forall x, (forall y, wf_strict_order.lt y x -> P y) -> P x) : P x.
wf_strict_order.wf_rec P H x

(* structures with a weak and a strict order *)

structure order_pair [class] (A : Type) extends weak_order A, has_lt A.
(le_of_lt : forall a b, lt a b -> le a b)
(lt_of_lt_of_le : forall a b c, lt a b -> le b c -> lt a c)
(lt_of_le_of_lt : forall a b c, le a b -> lt b c -> lt a c)
(lt_irrefl : forall a, ¬ lt a a)

section
  variable [s : order_pair A]
  variables {a b c : A}
  include s

Definition le_of_lt : a < b -> a ≤ b . !order_pair.le_of_lt

Definition lt_of_lt_of_le [trans] : a < b -> b ≤ c -> a < c . !order_pair.lt_of_lt_of_le

Definition lt_of_le_of_lt [trans] : a ≤ b -> b < c -> a < c . !order_pair.lt_of_le_of_lt

  privateDefinition lt_irrefl (s' : order_pair A) (a : A) : ¬ a < a . !order_pair.lt_irrefl

  privateDefinition lt_trans (s' : order_pair A) (a b c: A) (lt_ab : a < b) (lt_bc : b < c) : a < c.
  lt_of_lt_of_le lt_ab (le_of_lt lt_bc)

Definition order_pair.to_strict_order [trans_instance] : strict_order A.
  ( strict_order, s, lt_irrefl . lt_irrefl s, lt_trans . lt_trans s )

Definition gt_of_gt_of_ge [trans] (H1 : a > b) (H2 : b ≥ c) : a > c . lt_of_le_of_lt H2 H1

Definition gt_of_ge_of_gt [trans] (H1 : a ≥ b) (H2 : b > c) : a > c . lt_of_lt_of_le H2 H1

Definition not_le_of_gt (H : a > b) : ¬ a ≤ b.
  assume H1 : a ≤ b,
  lt.irrefl _ (lt_of_lt_of_le H H1)

Definition not_lt_of_ge (H : a ≥ b) : ¬ a < b.
  assume H1 : a < b,
  lt.irrefl _ (lt_of_le_of_lt H H1)
Defined.

structure strong_order_pair [class] (A : Type) extends weak_order A, has_lt A.
(le_iff_lt_sum_eq : forall a b, le a b ↔ lt a b ⊎ a = b)
(lt_irrefl : forall a, ¬ lt a a)

Definition le_iff_lt_sum_eq [s : strong_order_pair A] {a b : A} : a ≤ b ↔ a < b ⊎ a = b.
!strong_order_pair.le_iff_lt_sum_eq

Definition lt_sum_eq_of_le [s : strong_order_pair A] {a b : A} (le_ab : a ≤ b) : a < b ⊎ a = b.
iff.mp le_iff_lt_sum_eq le_ab

Definition le_of_lt_sum_eq [s : strong_order_pair A] {a b : A} (lt_sum_eq : a < b ⊎ a = b) : a ≤ b.
iff.mpr le_iff_lt_sum_eq lt_sum_eq

privateDefinition lt_irrefl' [s : strong_order_pair A] (a : A) : ¬ a < a.
!strong_order_pair.lt_irrefl

privateDefinition le_of_lt' [s : strong_order_pair A] (a b : A) : a < b -> a ≤ b.
take Hlt, le_of_lt_sum_eq (sum.inl Hlt)

privateDefinition lt_iff_le_prod_ne [s : strong_order_pair A] {a b : A} : a < b ↔ (a ≤ b \* a ≠ b).
iff.intro
  (take Hlt, pair (le_of_lt_sum_eq (sum.inl Hlt)) (take Hab, absurd (Hab # Hlt) !lt_irrefl'))
  (take Hand,
  have Hor : a < b ⊎ a = b, from lt_sum_eq_of_le (prod.pr1 Hand),
  sum_resolve_left Hor (prod.pr2 Hand))

Definition lt_of_le_of_ne [s : strong_order_pair A] {a b : A} : a ≤ b -> a ≠ b -> a < b.
take H1 H2, iff.mpr lt_iff_le_prod_ne (pair H1 H2)

privateDefinition ne_of_lt' [s : strong_order_pair A] {a b : A} (H : a < b) : a ≠ b.
prod.pr2 ((iff.mp (@lt_iff_le_prod_ne _ _ _ _)) H)

privateDefinition lt_of_lt_of_le' [s : strong_order_pair A] (a b c : A) : a < b -> b ≤ c -> a < c.
assume lt_ab : a < b,
assume le_bc : b ≤ c,
have le_ac : a ≤ c, from le.trans (le_of_lt' _ _ lt_ab) le_bc,
have ne_ac : a ≠ c, from
  assume eq_ac : a = c,
  have le_ba : b ≤ a, from eq_ac^-1 # le_bc,
  have eq_ab : a = b, from le.antisymm  (le_of_lt' _ _ lt_ab) le_ba,
  show empty, from ne_of_lt' lt_ab eq_ab,
show a < c, from iff.mpr (lt_iff_le_prod_ne) (pair le_ac ne_ac)

Definition lt_of_le_of_lt' [s : strong_order_pair A] (a b c : A) : a ≤ b -> b < c -> a < c.
assume le_ab : a ≤ b,
assume lt_bc : b < c,
have le_ac : a ≤ c, from le.trans le_ab (le_of_lt' _ _ lt_bc),
have ne_ac : a ≠ c, from
  assume eq_ac : a = c,
  have le_cb : c ≤ b, from eq_ac # le_ab,
  have eq_bc : b = c, from le.antisymm  (le_of_lt' _ _ lt_bc) le_cb,
  show empty, from ne_of_lt' lt_bc eq_bc,
show a < c, from iff.mpr (lt_iff_le_prod_ne) (pair le_ac ne_ac)

Definition strong_order_pair.to_order_pair [trans_instance] [s : strong_order_pair A] : order_pair A.
( order_pair, s,
  lt_irrefl . lt_irrefl',
  le_of_lt . le_of_lt',
  lt_of_le_of_lt . lt_of_le_of_lt',
  lt_of_lt_of_le . lt_of_lt_of_le' )

(* linear orders *)

structure linear_order_pair [class] (A : Type) extends order_pair A, linear_weak_order A

structure linear_strong_order_pair [class] (A : Type) extends strong_order_pair A,
  linear_weak_order A

Definition linear_strong_order_pair.to_linear_order_pair [trans_instance]
  [s : linear_strong_order_pair A] : linear_order_pair A.
( linear_order_pair, s, strong_order_pair.to_order_pair )

section
  variable [s : linear_strong_order_pair A]
  variables (a b c : A)
  include s

Definition lt.trichotomy : a < b ⊎ a = b ⊎ b < a.
  sum.elim (le.total a b)
  (assume H : a ≤ b,
  sum.elim (iff.mp !le_iff_lt_sum_eq H) (assume H1, sum.inl H1) (assume H1, sum.inr (sum.inl H1)))
  (assume H : b ≤ a,
  sum.elim (iff.mp !le_iff_lt_sum_eq H)
  (assume H1, sum.inr (sum.inr H1))
  (assume H1, sum.inr (sum.inl (H1^-1))))

Definition lt.by_cases {a b : A} {P : Type}
  (H1 : a < b -> P) (H2 : a = b -> P) (H3 : b < a -> P) : P.
  sum.elim !lt.trichotomy
  (assume H, H1 H)
  (assume H, sum.elim H (assume H', H2 H') (assume H', H3 H'))

Definition lt_ge_by_cases {a b : A} {P : Type} (H1 : a < b -> P) (H2 : a ≥ b -> P) : P.
  lt.by_cases H1 (fun H => H2 (H # le.refl a)) (fun H => H2 (le_of_lt H))

Definition le_of_not_gt {a b : A} (H : ¬ a > b) : a ≤ b.
  lt.by_cases (assume H', absurd H' H) (assume H', H' # !le.refl) (assume H', le_of_lt H')

Definition lt_of_not_ge {a b : A} (H : ¬ a ≥ b) : a < b.
  lt.by_cases
  (assume H', absurd (le_of_lt H') H)
  (assume H', absurd (H' # !le.refl) H)
  (assume H', H')

Definition lt_sum_ge : a < b ⊎ a ≥ b.
  lt.by_cases
  (assume H1 : a < b, sum.inl H1)
  (assume H1 : a = b, sum.inr (H1 # le.refl a))
  (assume H1 : a > b, sum.inr (le_of_lt H1))

Definition le_sum_gt : a ≤ b ⊎ a > b.
  !sum.swap (lt_sum_ge b a)

Definition lt_sum_gt_of_ne {a b : A} (H : a ≠ b) : a < b ⊎ a > b.
  lt.by_cases (assume H1, sum.inl H1) (assume H1, absurd H1 H) (assume H1, sum.inr H1)
Defined.

open decidable

structure decidable_linear_order [class] (A : Type) extends linear_strong_order_pair A.
(decidable_lt : decidable_rel lt)

section
  variable [s : decidable_linear_order A]
  variables {a b c d : A}
  include s
  open decidable

Definition decidable_lt [instance] : decidable (a < b).
  @decidable_linear_order.decidable_lt _ _ _ _

Definition decidable_le [instance] : decidable (a ≤ b).
  by_cases
  (assume H : a < b, inl (le_of_lt H))
  (assume H : ¬ a < b,
  have H1 : b ≤ a, from le_of_not_gt H,
  by_cases
  (assume H2 : b < a, inr (not_le_of_gt H2))
  (assume H2 : ¬ b < a, inl (le_of_not_gt H2)))

Definition has_decidable_eq [instance] : decidable (a = b).
  by_cases
  (assume H : a ≤ b,
  by_cases
  (assume H1 : b ≤ a, inl (le.antisymm H H1))
  (assume H1 : ¬ b ≤ a, inr (assume H2 : a = b, H1 (H2 # le.refl a))))
  (assume H : ¬ a ≤ b,
  (inr (assume H1 : a = b, H (H1 # !le.refl))))

Definition eq_sum_lt_of_not_lt {a b : A} (H : ¬ a < b) : a = b ⊎ b < a.
  if Heq : a = b then sum.inl Heq else sum.inr (lt_of_not_ge (fun Hge => H (lt_of_le_of_ne Hge Heq)))

Definition eq_sum_lt_of_le {a b : A} (H : a ≤ b) : a = b ⊎ a < b.
Proof.
  cases eq_sum_lt_of_not_lt (not_lt_of_ge H),
  exact sum.inl a_1^-1,
  exact sum.inr a_1
Defined.


  (* testing equality first may result in moreDefinitional equalities *)
Definition lt.cases {B : Type} (a b : A) (t_lt t_eq t_gt : B) : B.
  if a = b then t_eq else (if a < b then t_lt else t_gt)

Definition lt.cases_of_eq {B : Type} {a b : A} {t_lt t_eq t_gt : B} (H : a = b) :
  lt.cases a b t_lt t_eq t_gt = t_eq . if_pos H

Definition lt.cases_of_lt {B : Type} {a b : A} {t_lt t_eq t_gt : B} (H : a < b) :
  lt.cases a b t_lt t_eq t_gt = t_lt.
  if_neg (ne_of_lt H) @ if_pos H

Definition lt.cases_of_gt {B : Type} {a b : A} {t_lt t_eq t_gt : B} (H : a > b) :
  lt.cases a b t_lt t_eq t_gt = t_gt.
  if_neg (ne.symm (ne_of_lt H)) @ if_neg (lt.asymm H)

Definition min (a b : A) : A . if a ≤ b then a else b
Definition max (a b : A) : A . if a ≤ b then b else a

  (* these show min and max form a lattice *)

Definition min_le_left (a b : A) : min a b ≤ a.
  by_cases
  (assume H : a ≤ b, by rewrite [↑min, if_pos H])
  (assume H : ¬ a ≤ b, by rewrite [↑min, if_neg H]; apply le_of_lt (lt_of_not_ge H))

Definition min_le_right (a b : A) : min a b ≤ b.
  by_cases
  (assume H : a ≤ b, by rewrite [↑min, if_pos H]; apply H)
  (assume H : ¬ a ≤ b, by rewrite [↑min, if_neg H])

Definition le_min {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) : c ≤ min a b.
  by_cases
  (assume H : a ≤ b, by rewrite [↑min, if_pos H]; apply H₁)
  (assume H : ¬ a ≤ b, by rewrite [↑min, if_neg H]; apply H₂)

Definition le_max_left (a b : A) : a ≤ max a b.
  by_cases
  (assume H : a ≤ b, by rewrite [↑max, if_pos H]; apply H)
  (assume H : ¬ a ≤ b, by rewrite [↑max, if_neg H])

Definition le_max_right (a b : A) : b ≤ max a b.
  by_cases
  (assume H : a ≤ b, by rewrite [↑max, if_pos H])
  (assume H : ¬ a ≤ b, by rewrite [↑max, if_neg H]; apply le_of_lt (lt_of_not_ge H))

Definition max_le {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) : max a b ≤ c.
  by_cases
  (assume H : a ≤ b, by rewrite [↑max, if_pos H]; apply H₂)
  (assume H : ¬ a ≤ b, by rewrite [↑max, if_neg H]; apply H₁)

Definition le_max_left_iff_unit (a b : A) : a ≤ max a b ↔ unit.
  iff_unit_intro (le_max_left a b)

Definition le_max_right_iff_unit (a b : A) : b ≤ max a b ↔ unit.
  iff_unit_intro (le_max_right a b)

  (* these are also proved for lattices, but with inf and sup in place of min and max *)

Definition eq_min {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) (H₃ : forall {d}, d ≤ a -> d ≤ b -> d ≤ c) :
  c = min a b.
  le.antisymm (le_min H₁ H₂) (H₃ !min_le_left !min_le_right)

Definition min.comm (a b : A) : min a b = min b a.
  eq_min !min_le_right !min_le_left (fun c H₁ H₂ => le_min H₂ H₁)

Definition min.assoc (a b c : A) : min (min a b) c = min a (min b c).
Proof.
  apply eq_min,
  { apply le.trans, apply min_le_left, apply min_le_left },
  { apply le_min, apply le.trans, apply min_le_left, apply min_le_right, apply min_le_right },
  { intros [d, H₁, H₂], apply le_min, apply le_min H₁, apply le.trans H₂, apply min_le_left,
  apply le.trans H₂, apply min_le_right }
Defined.

Definition min.left_comm (a b c : A) : min a (min b c) = min b (min a c).
  binary.left_comm (@min.comm A s) (@min.assoc A s) a b c

Definition min.right_comm (a b c : A) : min (min a b) c = min (min a c) b.
  binary.right_comm (@min.comm A s) (@min.assoc A s) a b c

Definition min_self (a : A) : min a a = a.
  by apply inverse; apply eq_min (le.refl a) !le.refl; intros; assumption

Definition min_eq_left {a b : A} (H : a ≤ b) : min a b = a.
  by apply inverse; apply eq_min !le.refl H; intros; assumption

Definition min_eq_right {a b : A} (H : b ≤ a) : min a b = b.
  eq.subst !min.comm (min_eq_left H)

Definition eq_max {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) (H₃ : forall {d}, a ≤ d -> b ≤ d -> c ≤ d) :
  c = max a b.
  le.antisymm (H₃ !le_max_left !le_max_right) (max_le H₁ H₂)

Definition max.comm (a b : A) : max a b = max b a.
  eq_max !le_max_right !le_max_left (fun c H₁ H₂ => max_le H₂ H₁)

Definition max.assoc (a b c : A) : max (max a b) c = max a (max b c).
Proof.
  apply eq_max,
  { apply le.trans, apply le_max_left a b, apply le_max_left },
  { apply max_le, apply le.trans, apply le_max_right a b, apply le_max_left, apply le_max_right },
  { intros [d, H₁, H₂], apply max_le, apply max_le H₁, apply le.trans !le_max_left H₂,
  apply le.trans !le_max_right H₂}
Defined.

Definition max.left_comm (a b c : A) : max a (max b c) = max b (max a c).
  binary.left_comm (@max.comm A s) (@max.assoc A s) a b c

Definition max.right_comm (a b c : A) : max (max a b) c = max (max a c) b.
  binary.right_comm (@max.comm A s) (@max.assoc A s) a b c

Definition max_self (a : A) : max a a = a.
  by apply inverse; apply eq_max (le.refl a) !le.refl; intros; assumption

Definition max_eq_left {a b : A} (H : b ≤ a) : max a b = a.
  by apply inverse; apply eq_max !le.refl H; intros; assumption

Definition max_eq_right {a b : A} (H : a ≤ b) : max a b = b.
  eq.subst !max.comm (max_eq_left H)

  (* these rely on lt_of_lt *)

Definition min_eq_left_of_lt {a b : A} (H : a < b) : min a b = a.
  min_eq_left (le_of_lt H)

Definition min_eq_right_of_lt {a b : A} (H : b < a) : min a b = b.
  min_eq_right (le_of_lt H)

Definition max_eq_left_of_lt {a b : A} (H : b < a) : max a b = a.
  max_eq_left (le_of_lt H)

Definition max_eq_right_of_lt {a b : A} (H : a < b) : max a b = b.
  max_eq_right (le_of_lt H)

  (* these use the fact that it is a linear ordering *)

Definition lt_min {a b c : A} (H₁ : a < b) (H₂ : a < c) : a < min b c.
  sum.elim !le_sum_gt
  (assume H : b ≤ c, by rewrite (min_eq_left H); apply H₁)
  (assume H : b > c, by rewrite (min_eq_right_of_lt H); apply H₂)

Definition max_lt {a b c : A} (H₁ : a < c) (H₂ : b < c) : max a b < c.
  sum.elim !le_sum_gt
  (assume H : a ≤ b, by rewrite (max_eq_right H); apply H₂)
  (assume H : a > b, by rewrite (max_eq_left_of_lt H); apply H₁)
Defined.
Defined. algebra
