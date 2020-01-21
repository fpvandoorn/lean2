(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Terminal category
*)

import .indiscrete

open functor is_trunc unit eq

namespace category

Definition terminal_precategory : precategory unit.
  indiscrete_precategory unit

Definition Terminal_precategory : Precategory.
  precategory.Mk terminal_precategory

  notation 1 . Terminal_precategory
Definition one_op : 1ᵒᵖ = 1 . idp

Definition terminal_functor (C : Precategory) : C ⇒ 1.
  functor.mk (fun x => star)
             (fun x y f => star)
             (fun x => idp)
             (fun x y z g f => idp)

Definition is_contr_functor_one [instance] (C : Precategory) : is_contr (C ⇒ 1).
  is_contr.mk (terminal_functor C)
              begin
                intro F, fapply functor_eq =>
                { intro x, apply @is_prop.elim unit},
                { intro x y f, apply @is_prop.elim unit}
              end

Definition terminal_functor_op (C : Precategory)
    : (terminal_functor C)ᵒᵖᶠ = terminal_functor Cᵒᵖ . idp

Definition terminal_functor_comp {C D : Precategory} (F : C ⇒ D)
    : (terminal_functor D) of F = terminal_functor C . idp

Definition point (C : Precategory) (c : C) : 1 ⇒ C.
  functor.mk (fun x => c)
             (fun x y f => id)
             (fun x => idp)
             (fun x y z g f => !id_id^-1)

  (* we need id_id in the declaration of precategory to make this to holdDefinitionally *)
Definition point_op (C : Precategory) (c : C) : (point C c)ᵒᵖᶠ = point Cᵒᵖ c . idp

Definition point_comp {C D : Precategory} (F : C ⇒ D) (c : C)
    : F of point C c = point D (F c) . idp

Defined. category
