(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Initial category
*)

import .indiscrete

open functor is_trunc eq

namespace category

Definition initial_precategory : precategory empty.
  indiscrete_precategory empty

Definition Initial_precategory : Precategory.
  precategory.Mk initial_precategory

  notation 0 . Initial_precategory
Definition zero_op : 0ᵒᵖ = 0 . idp

Definition initial_functor (C : Precategory) : 0 ⇒ C.
  functor.mk (fun x => empty.elim x)
             (fun x y f => empty.elim x)
             (fun x => empty.elim x)
             (fun x y z g f => empty.elim x)

Definition is_contr_initial_functor [instance] (C : Precategory) : is_contr (0 ⇒ C).
  is_contr.mk (initial_functor C)
              begin
                intro F, fapply functor_eq =>
                { intro x, exact empty.elim x},
                { intro x y f, exact empty.elim x}
              end

Definition initial_functor_op (C : Precategory)
    : (initial_functor C)ᵒᵖᶠ = initial_functor Cᵒᵖ.
  by apply @is_prop.elim (0 ⇒ Cᵒᵖ)

Definition initial_functor_comp {C D : Precategory} (F : C ⇒ D)
    : F of initial_functor C = initial_functor D.
  by apply @is_prop.elim (0 ⇒ D)

Defined. category
