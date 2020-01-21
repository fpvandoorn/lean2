(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
*)
prelude
import init.datatypes

notation `assume` binders `,` r:(scoped f, f) . r
notation `take`   binders `,` r:(scoped f, f) . r

structure has_zero    [class] (A : Type) . (zero : A)
structure has_one     [class] (A : Type) . (one : A)
structure has_add     [class] (A : Type) . (add : A -> A -> A)
structure has_mul     [class] (A : Type) . (mul : A -> A -> A)
structure has_inv     [class] (A : Type) . (inv : A -> A)
structure has_neg     [class] (A : Type) . (neg : A -> A)
structure has_sub     [class] (A : Type) . (sub : A -> A -> A)
structure has_div     [class] (A : Type) . (div : A -> A -> A)
structure has_mod     [class] (A : Type) . (mod : A -> A -> A)
structure has_dvd.{l} [class] (A : Type.{l}) : Type.{l+1} . (dvd : A -> A -> Type.{l})
structure has_le.{l}  [class] (A : Type.{l}) : Type.{l+1} . (le : A -> A -> Type.{l})
structure has_lt.{l}  [class] (A : Type.{l}) : Type.{l+1} . (lt : A -> A -> Type.{l})

Definition zero {A : Type} [s : has_zero A] : A            . has_zero.zero A
Definition one  {A : Type} [s : has_one A]  : A            . has_one.one A
Definition add  {A : Type} [s : has_add A]  : A -> A -> A    . has_add.add
Definition mul              {A : Type} [s : has_mul A]  : A -> A -> A    . has_mul.mul
Definition sub              {A : Type} [s : has_sub A]  : A -> A -> A    . has_sub.sub
Definition div              {A : Type} [s : has_div A]  : A -> A -> A    . has_div.div
Definition dvd              {A : Type} [s : has_dvd A]  : A -> A -> Type . has_dvd.dvd
Definition mod              {A : Type} [s : has_mod A]  : A -> A -> A    . has_mod.mod
Definition neg              {A : Type} [s : has_neg A]  : A -> A        . has_neg.neg
Definition inv              {A : Type} [s : has_inv A]  : A -> A        . has_inv.inv
Definition le               {A : Type} [s : has_le A]   : A -> A -> Type . has_le.le
Definition lt               {A : Type} [s : has_lt A]   : A -> A -> Type . has_lt.lt

Definition ge {A : Type} [s : has_le A] (a b : A) : Type . le b a
Definition gt {A : Type} [s : has_lt A] (a b : A) : Type . lt b a

(*
  bit0 and bit1 are two auxiliaryDefinition used when parsing numerals such as 13, 0, 26.
  The parser will generate the terms (bit1 (bit0 (bit1 one))), zero, and
  (bit0 (bit1 (bit0 (bit1 one)))). This works in any type with an addition, a zero and a one.
  More specifically, there must be type class instances for the classes for has_add, has_zero and
  has_one
*)
Definition bit0 {A : Type} [s  : has_add A] (a  : A)                 : A . add a a
Definition bit1 {A : Type} [s₁ : has_one A] [s₂ : has_add A] (a : A) : A.
add (bit0 a) one

Definition num_has_zero [instance]  : has_zero num.
has_zero.mk num.zero

Definition num_has_one [instance] : has_one num.
has_one.mk (num.pos pos_num.one)

Definition pos_num_has_one [instance] : has_one pos_num.
has_one.mk (pos_num.one)

namespace pos_num
  open bool
Definition is_one (a : pos_num) : bool.
  pos_num.rec_on a tt (fun n r => ff) (fun n r => ff)

Definition pred (a : pos_num) : pos_num.
  pos_num.rec_on a one (fun n r => bit0 n) (fun n r => bool.rec_on (is_one n) (bit1 r) one)

Definition size (a : pos_num) : pos_num.
  pos_num.rec_on a one (fun n r => succ r) (fun n r => succ r)

Definition add (a b : pos_num) : pos_num.
  pos_num.rec_on a
    succ
    (fun n f b => pos_num.rec_on b
      (succ (bit1 n))
      (fun m r => succ (bit1 (f m)))
      (fun m r => bit1 (f m)))
    (fun n f b => pos_num.rec_on b
      (bit1 n)
      (fun m r => bit1 (f m))
      (fun m r => bit0 (f m)))
    b
Defined. pos_num

Definition pos_num_has_add [instance] : has_add pos_num.
has_add.mk pos_num.add

namespace num
  open pos_num

Definition add (a b : num) : num.
  num.rec_on a b (fun pa => num.rec_on b (pos pa) (fun pb => pos (pos_num.add pa pb)))
Defined. num

Definition num_has_add [instance] : has_add num.
has_add.mk num.add

Definition std.priority.default : num . 1000
Definition std.priority.max     : num . 4294967295

namespace nat
  protectedDefinition prio . num.add std.priority.default 100

  protectedDefinition add (a b : nat) : nat.
  nat.rec a (fun b₁ r => succ r) b

Definition of_num (n : num) : nat.
  num.rec zero
    (fun n => pos_num.rec (succ zero) (fun n r => nat.add (nat.add r r) (succ zero)) (fun n r => nat.add r r) n) n
Defined. nat


          [instance] [priority nat.prio]

Definition nat_has_zero [instance] [priority nat.prio] : has_zero nat.
has_zero.mk nat.zero

Definition nat_has_one [instance] [priority nat.prio] : has_one nat.
has_one.mk (nat.succ (nat.zero))

Definition nat_has_add [instance] [priority nat.prio] : has_add nat.
has_add.mk nat.add

(*
  Global declarations of right binding strength

  If a module reassigns these, it will be incompatible with other modules that adhere to these
  conventions.

  When hovering over a symbol, use "C-c C-k" to see how to input it.
*)
Definition std.prec.max   : num . 1024 (* the strength of application, identifiers, (, [, etc. *)
Definition std.prec.arrow : num . 25

(*
The nextDefinition is "max + 10". It can be used e.g. for postfix operations that should
be stronger than application.
*)

Definition std.prec.max_plus.
num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ
  (num.succ std.prec.max)))))))))

(* Logical operations and relations *)

reserve prefix `¬`:40
reserve prefix `~`:40
reserve infixr ` ∧ `:35
reserve infixr ` /\ `:35
reserve infixr ` \/ `:30
reserve infixr ` ∨ `:30
reserve infix ` <-> `:20
reserve infix ` ↔ `:20
reserve infix ` = `:50
reserve infix ` ≠ `:50
reserve infix ` ≈ `:50
reserve infix ` == `:50
reserve infix ` ≡ `:50

reserve infixr ` o `:60                 (* input with \comp *)
reserve postfix `^-1`:std.prec.max_plus  (* input with \sy or \-1 or \inv *)

reserve infixl ` @ `:75
reserve infixr ` # `:75
reserve infixr ` ▹ `:75

(* types and type constructors *)

reserve infixr ` ⊎ `:30
reserve infixr ` \* `:35

(* arithmetic operations *)

reserve infixl ` + `:65
reserve infixl ` - `:65
reserve infixl ` * `:70
reserve infixl ` / `:70
reserve infixl ` % `:70
reserve prefix `-`:100
reserve infix ` ^ `:80

reserve infix ` <= `:50
reserve infix ` ≤ `:50
reserve infix ` < `:50
reserve infix ` >= `:50
reserve infix ` ≥ `:50
reserve infix ` > `:50

(* boolean operations *)

reserve infixl ` && `:70
reserve infixl ` || `:65

(* set operations *)

reserve infix ` ∈ `:50
reserve infix ` ∉ `:50
reserve infixl ` ∩ `:70
reserve infixl ` ∪ `:65
reserve infix ` ⊆ `:50
reserve infix ` ⊇ `:50

(* other symbols *)

reserve infix ` ∣ `:50
reserve infixl ` ++ `:65
reserve infixr ` :: `:67

(*
  in the HoTT library we might not always want to overload the following notation,
  so we put it in namespace algebra
*)

infix +    . add
infix *    . mul
infix -    . sub
infix /    . div
infix ∣    . dvd
infix %    . mod
prefix -   . neg
namespace algebra
postfix ^-1 . inv
Defined. algebra
infix ≤    . le
infix ≥    . ge
infix <    . lt
infix >    . gt

notation [parsing_only] x ` +[`:65 A:0 `] `:0 y:65 . @add A _ x y
notation [parsing_only] x ` -[`:65 A:0 `] `:0 y:65 . @sub A _ x y
notation [parsing_only] x ` *[`:70 A:0 `] `:0 y:70 . @mul A _ x y
notation [parsing_only] x ` /[`:70 A:0 `] `:0 y:70 . @div A _ x y
notation [parsing_only] x ` ∣[`:70 A:0 `] `:0 y:70 . @dvd A _ x y
notation [parsing_only] x ` %[`:70 A:0 `] `:0 y:70 . @mod A _ x y
notation [parsing_only] x ` ≤[`:50 A:0 `] `:0 y:50 . @le A _ x y
notation [parsing_only] x ` ≥[`:50 A:0 `] `:0 y:50 . @ge A _ x y
notation [parsing_only] x ` <[`:50 A:0 `] `:0 y:50 . @lt A _ x y
notation [parsing_only] x ` >[`:50 A:0 `] `:0 y:50 . @gt A _ x y
