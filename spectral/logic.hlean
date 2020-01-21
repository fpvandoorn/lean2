(*
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
*)
import types.trunc
open funext eq trunc is_trunc prod sum

--reserve prefix `¬`:40
--reserve prefix `~`:40
--reserve infixr ` ∧ `:35
--reserve infixr ` /\ `:35
--reserve infixr ` \/ `:30
--reserve infixr ` ∨ `:30
--reserve infix ` <-> `:20
--reserve infix ` ↔ `:20

namespace logic

section
open trunc_index

Definition propext {p q : Prop} (h : p ↔ q) : p = q.
tua (equiv_of_iff_of_is_prop h _ _)

Defined.

Definition false : Prop . trunctype.mk (lift empty) _

Definition false.elim {A : Type} (h : false) : A . lift.rec empty.elim h

Definition true : Prop . trunctype.mk (lift unit) _

Definition true.intro : true . lift.up unit.star

Definition trivial : true . lift.up unit.star

Definition and (p q : Prop) : Prop . tprod p q

infixr ` ∧ ` . and
infixr ` /\ ` . and

Definition and.intro {p q : Prop} (h₁ : p) (h₂ : q) : and p q . prod.mk h₁ h₂

Definition and.left {p q : Prop} (h : p ∧ q) : p . prod.pr1 h

Definition and.right {p q : Prop} (h : p ∧ q) : q . prod.pr2 h

Definition not (p : Prop) : Prop . trunctype.mk (p -> empty) _

Definition or.inl . @or.intro_left

Definition or.inr . @or.intro_right

Definition or.elim {A B C : Type} [is_prop C] (h₀ : A ∨ B) (h₁ : (A -> C)) (h₂ : B -> C) : C.
Proof.
  apply trunc.elim_on h₀,
  intro h₃,
  apply sum.elim h₃ h₁ h₂
Defined.

Defined. logic
