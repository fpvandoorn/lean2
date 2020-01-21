(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jakob von Raumer

Basic datatypes
*)

prelude
notation [parsing_only] `Type'` . Type.{_+1}
notation [parsing_only] `Type₊` . Type.{_+1}
notation `Type₀` . Type.{0}
notation `Type₁` . Type.{1}
notation `Type₂` . Type.{2}
notation `Type₃` . Type.{3}

inductive poly_unit.{l} : Type.{l}.
star : poly_unit

inductive unit : Type₀.
star : unit

inductive empty : Type₀

inductive eq.{l} {A : Type.{l}} (a : A) : A -> Type.{l}.
refl : eq a a

structure lift.{l₁ l₂} (A : Type.{l₁}) : Type.{max l₁ l₂}.
up :: (down : A)

inductive prod (A B : Type).
mk : A -> B -> prod A B

Definition prod.pr1 {A B : Type} (p : prod A B) : A.
prod.rec (fun a b => a) p

Definition prod.pr2 {A B : Type} (p : prod A B) : B.
prod.rec (fun a b => b) p

Definition prod.destruct . @prod.cases_on

inductive sum (A B : Type) : Type.
| inl {} : A -> sum A B
| inr {} : B -> sum A B

Definition sum.intro_left {A : Type} (B : Type) (a : A) : sum A B.
sum.inl a

Definition sum.intro_right (A : Type) {B : Type} (b : B) : sum A B.
sum.inr b

inductive sigma {A : Type} (B : A -> Type).
mk : forall (a : A), B a -> sigma B

Definition sigma.pr1 {A : Type} {B : A -> Type} (p : sigma B) : A.
sigma.rec (fun a b => a) p

Definition sigma.pr2 {A : Type} {B : A -> Type} (p : sigma B) : B (sigma.pr1 p).
sigma.rec (fun a b => b) p

(* pos_num and num are two auxiliary datatypes used when parsing numerals such as 13, 0, 26 *)
(* in an [priority n] flag. *)
inductive pos_num : Type.
| one  : pos_num
| bit1 : pos_num -> pos_num
| bit0 : pos_num -> pos_num

namespace pos_num
Definition succ (a : pos_num) : pos_num.
  pos_num.rec_on a (bit0 one) (fun n r => bit0 r) (fun n r => bit1 n)
Defined. pos_num

inductive num : Type.
| zero  : num
| pos   : pos_num -> num

namespace num
  open pos_num
Definition succ (a : num) : num.
  num.rec_on a (pos one) (fun p => pos (succ p))
Defined. num

inductive bool : Type.
| ff : bool
| tt : bool

inductive char : Type.
mk : bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> char

inductive string : Type.
| empty : string
| str   : char -> string -> string

inductive option (A : Type) : Type.
| none {} : option A
| some    : A -> option A

(* Remark: we manually generate the nat.rec_on, nat.induction_on, nat.cases_on and nat.no_confusion. *)
(* We do that because we want 0 instead of nat.zero in these eliminators. *)
set_option inductive.rec_on   false
set_option inductive.cases_on false
inductive nat.
| zero : nat
| succ : nat -> nat
