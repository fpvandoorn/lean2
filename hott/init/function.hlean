(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

General operations on functions.
*)

prelude
import init.reserved_notation .types

open prod

namespace function

variables {A B C D E : Type}

Definition compose [unfold_full] (f : B -> C) (g : A -> B) : A -> C.
fun x => f (g x)

Definition compose_right [unfold_full] (f : B -> B -> B) (g : A -> B) : B -> A -> B.
fun b a => f b (g a)

Definition compose_left [unfold_full] (f : B -> B -> B) (g : A -> B) : A -> B -> B.
fun a b => f (g a) b

Definition on_fun [unfold_full] (f : B -> B -> C) (g : A -> B) : A -> A -> C.
fun x y => f (g x) (g y)

Definition combine [unfold_full] (f : A -> B -> C) (op : C -> D -> E) (g : A -> B -> D)
  : A -> B -> E.
fun x y => op (f x y) (g x y)

Definition const [unfold_full] (B : Type) (a : A) : B -> A.
fun x => a

Definition dcompose [unfold_full] {B : A -> Type} {C : forall {x : A}, B x -> Type}
  (f : forall {x : A} (y : B x), C y) (g : forall x, B x) : forall x, C (g x).
fun x => f (g x)

Definition flip [unfold_full] {C : A -> B -> Type} (f : forall x y, C x y) : forall y x, C x y.
fun y x => f x y

Definition app [unfold_full] {B : A -> Type} (f : forall x, B x) (x : A) : B x.
f x

Definition curry [unfold_full] : (A \* B -> C) -> A -> B -> C.
fun f a b => f (a, b)

Definition uncurry : (A -> B -> C) -> (A \* B -> C).
fun f p => match p with (a, b) . f a b end


infixr  ` o `            . compose
infixr  ` o' `:60        . dcompose
infixl  ` on `:1         . on_fun
infixr  ` $ `:1          . app
notation f ` -[` op `]- ` g  . combine f op g

Defined. function

(* copy reducible annotations to top-level *)
export [unfold] function
