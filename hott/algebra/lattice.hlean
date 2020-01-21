(*
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
*)
import .order

open eq

variable {A : Type}
set_option class.force_new true

(* lattices (we could split this to upper- and lower-semilattices, if needed) *)

namespace algebra
structure lattice [class] (A : Type) extends weak_order A.
(inf : A -> A -> A)
(sup : A -> A -> A)
(inf_le_left : forall a b, le (inf a b) a)
(inf_le_right : forall a b, le (inf a b) b)
(le_inf : forall a b c, le c a -> le c b -> le c (inf a b))
(le_sup_left : forall a b, le a (sup a b))
(le_sup_right : forall a b, le b (sup a b))
(sup_le : forall a b c, le a c -> le b c -> le (sup a b) c)

Definition inf . @lattice.inf
Definition sup . @lattice.sup
infix ` ⊓ `:70 . inf
infix ` ⊔ `:65 . sup

section
  variable [s : lattice A]
  include s

Definition inf_le_left (a b : A) : a ⊓ b ≤ a . !lattice.inf_le_left

Definition inf_le_right (a b : A) : a ⊓ b ≤ b . !lattice.inf_le_right

Definition le_inf {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) : c ≤ a ⊓ b . !lattice.le_inf H₁ H₂

Definition le_sup_left (a b : A) : a ≤ a ⊔ b . !lattice.le_sup_left

Definition le_sup_right (a b : A) : b ≤ a ⊔ b . !lattice.le_sup_right

Definition sup_le {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) : a ⊔ b ≤ c . !lattice.sup_le H₁ H₂

  (* inf *)

Definition eq_inf {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) (H₃ : forall {d}, d ≤ a -> d ≤ b -> d ≤ c) :
  c = a ⊓ b.
  le.antisymm (le_inf H₁ H₂) (H₃ !inf_le_left !inf_le_right)

Definition inf.comm (a b : A) : a ⊓ b = b ⊓ a.
  eq_inf !inf_le_right !inf_le_left (fun c H₁ H₂ => le_inf H₂ H₁)

Definition inf.assoc (a b c : A) : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c).
Proof.
  apply eq_inf,
  { apply le.trans, apply inf_le_left, apply inf_le_left },
  { apply le_inf, apply le.trans, apply inf_le_left, apply inf_le_right, apply inf_le_right },
  { intros [d, H₁, H₂], apply le_inf, apply le_inf H₁, apply le.trans H₂, apply inf_le_left,
  apply le.trans H₂, apply inf_le_right }
Defined.

Definition inf.left_comm (a b c : A) : a ⊓ (b ⊓ c) = b ⊓ (a ⊓ c).
  binary.left_comm (@inf.comm A s) (@inf.assoc A s) a b c

Definition inf.right_comm (a b c : A) : (a ⊓ b) ⊓ c = (a ⊓ c) ⊓ b.
  binary.right_comm (@inf.comm A s) (@inf.assoc A s) a b c

Definition inf_self (a : A) : a ⊓ a = a.
  by apply inverse; apply eq_inf (le.refl a) !le.refl; intros; assumption

Definition inf_eq_left {a b : A} (H : a ≤ b) : a ⊓ b = a.
  by apply inverse; apply eq_inf !le.refl H; intros; assumption

Definition inf_eq_right {a b : A} (H : b ≤ a) : a ⊓ b = b.
  eq.subst !inf.comm (inf_eq_left H)

  (* sup *)

Definition eq_sup {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) (H₃ : forall {d}, a ≤ d -> b ≤ d -> c ≤ d) :
  c = a ⊔ b.
  le.antisymm (H₃ !le_sup_left !le_sup_right) (sup_le H₁ H₂)

Definition sup.comm (a b : A) : a ⊔ b = b ⊔ a.
  eq_sup !le_sup_right !le_sup_left (fun c H₁ H₂ => sup_le H₂ H₁)

Definition sup.assoc (a b c : A) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c).
Proof.
  apply eq_sup,
  { apply le.trans, apply le_sup_left a b, apply le_sup_left },
  { apply sup_le, apply le.trans, apply le_sup_right a b, apply le_sup_left, apply le_sup_right },
  { intros [d, H₁, H₂], apply sup_le, apply sup_le H₁, apply le.trans !le_sup_left H₂,
  apply le.trans !le_sup_right H₂}
Defined.

Definition sup.left_comm (a b c : A) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c).
  binary.left_comm (@sup.comm A s) (@sup.assoc A s) a b c

Definition sup.right_comm (a b c : A) : (a ⊔ b) ⊔ c = (a ⊔ c) ⊔ b.
  binary.right_comm (@sup.comm A s) (@sup.assoc A s) a b c

Definition sup_self (a : A) : a ⊔ a = a.
  by apply inverse; apply eq_sup (le.refl a) !le.refl; intros; assumption

Definition sup_eq_left {a b : A} (H : b ≤ a) : a ⊔ b = a.
  by apply inverse; apply eq_sup !le.refl H; intros; assumption

Definition sup_eq_right {a b : A} (H : a ≤ b) : a ⊔ b = b.
  eq.subst !sup.comm (sup_eq_left H)
Defined.

Defined. algebra
