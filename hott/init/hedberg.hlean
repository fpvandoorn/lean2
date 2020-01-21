(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Hedberg's Theorem: every type with decidable equality is a set
*)

prelude
import init.trunc
open eq eq.ops nat is_trunc sigma

(* TODO(Leo): move const coll and path_coll to a different file? *)
privateDefinition const {A B : Type} (f : A -> B) . ∀ x y, f x = f y
privateDefinition coll (A : Type) . Σ f : A -> A, const f
privateDefinition path_coll (A : Type) . ∀ x y : A, coll (x = y)

section
  parameter  {A : Type}
  hypothesis [h : decidable_eq A]
  variables  {x y : A}

  privateDefinition pc : path_coll A.
  fun a b => decidable.rec_on (h a b)
    (fun p  : a = b =>   ⟨(fun q => p), fun q r => rfl⟩)
    (fun np : ¬ a = b => ⟨(fun q => q), fun q r => absurd q np⟩)

  privateDefinition f : x = y -> x = y.
  sigma.rec_on (pc x y) (fun f c => f)

  privateDefinition f_const (p q : x = y) : f p = f q.
  sigma.rec_on (pc x y) (fun f c => c p q)

  privateDefinition aux (p : x = y) : p = (f (refl x))^-1 @ (f p).
  have aux : refl x = (f (refl x))^-1 @ (f (refl x)), from
    eq.rec_on (f (refl x)) rfl,
  eq.rec_on p aux

Definition is_set_of_decidable_eq : is_set A.
  is_set.mk A (fun x y p q => calc
   p   = (f (refl x))^-1 @ (f p) : aux
   ... = (f (refl x))^-1 @ (f q) : f_const
   ... = q                      : aux)
Defined.


