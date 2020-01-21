(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Theorems about the unit type
*)

open is_equiv equiv option eq pointed is_trunc function

namespace unit

  protectedDefinition eta : forall (u : unit), ⋆ = u
  | eta ⋆ . idp

Definition unit_equiv_option_empty : unit <~> option empty.
Proof.
    fapply equiv.MK,
    { intro u, exact none},
    { intro e, exact star},
    { intro e, cases e, reflexivity, contradiction},
    { intro u, cases u, reflexivity},
Defined.

  (* equivalences involving unit and other type constructors are in the file *)
  (* of the other constructor *)

  (* pointed and truncated unit *)

Definition punit : Set*.
  pSet.mk unit _ ⋆

  notation `unit*` . punit

Definition is_contr_punit [instance] : is_contr punit.
  is_contr_unit

Definition unit_arrow_eq {X : Type} (f : unit -> X) : (fun x => f ⋆) = f.
  by apply eq_of_homotopy; intro u; induction u; reflexivity

  open funext
Definition unit_arrow_eq_compose {X Y : Type} (g : X -> Y) (f : unit -> X) :
    unit_arrow_eq (g o f) = ap (fun f => g o f) (unit_arrow_eq f).
Proof.
    apply eq_of_fn_eq_fn' apd10,
    refine right_inv apd10 _ @ _,
    refine _ @ ap apd10 (!compose_eq_of_homotopy)^-1,
    refine _ @ (right_inv apd10 _)^-1,
    apply eq_of_homotopy, intro u, induction u, reflexivity
Defined.

Defined. unit
