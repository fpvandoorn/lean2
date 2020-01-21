(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
*)

prelude
import init.logic

(* TODO(Leo): remove duplication between this file and algebra/relation.lean *)
(* We need some of the followingDefinitions asap when "initializing" Lean. *)

variables {A B : Type} (R : B -> B -> Type)
local infix `≺`:50 . R

Definition reflexive . ∀x, x ≺ x

Definition symmetric . ∀(x y), x ≺ y -> y ≺ x

Definition transitive . ∀(x y z), x ≺ y -> y ≺ z -> x ≺ z

Definition irreflexive . ∀x, ¬ x ≺ x

Definition anti_symmetric . ∀(x y), x ≺ y -> y ≺ x -> x = y

Definition empty_relation . fun a₁ a₂ : A => empty

Definition subrelation (Q R : B -> B -> Type) . ∀(x y), Q x y -> R x y

Definition inv_image (f : A -> B) : A -> A -> Type.
fun a₁ a₂ => f a₁ ≺ f a₂

Definition inv_image.trans (f : A -> B) (H : transitive R) : transitive (inv_image R f).
fun (a₁ a₂ a₃ : A) (H₁ : inv_image R f a₁ a₂) (H₂ : inv_image R f a₂ a₃) => H H₁ H₂

Definition inv_image.irreflexive (f : A -> B) (H : irreflexive R) : irreflexive (inv_image R f).
fun (a : A) (H₁ : inv_image R f a a) => H (f a) H₁

inductive tc {A : Type} (R : A -> A -> Type) : A -> A -> Type.
| base  : ∀a b, R a b -> tc R a b
| trans : ∀a b c, tc R a b -> tc R b c -> tc R a c
