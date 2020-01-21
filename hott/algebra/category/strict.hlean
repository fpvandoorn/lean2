(*
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer
*)

import .functor.basic

open is_trunc eq

namespace category
  structure strict_precategory [class] (ob : Type) extends precategory ob.
  mk' :: (is_set_ob : is_set ob)

  attribute strict_precategory.is_set_ob [instance]

Definition strict_precategory.mk {ob : Type} (C : precategory ob)
    (H : is_set ob) : strict_precategory ob.
  precategory.rec_on C strict_precategory.mk' H

  structure Strict_precategory : Type.
    (carrier : Type)
    (struct : strict_precategory carrier)

  attribute Strict_precategory.struct [instance] [coercion]

Definition Strict_precategory.to_Precategory [coercion] [reducible]
    (C : Strict_precategory) : Precategory.
  Precategory.mk (Strict_precategory.carrier C) _

  open functor

  (* TODO: move to constructions.cat? *)
Definition precategory_strict_precategory : precategory Strict_precategory.
  precategory.mk (fun A B => A ⇒ B)
                 (fun A B C G F => G of F)
                 (fun A => 1)
                 (fun A B C D => functor.assoc)
                 (fun A B => functor.id_left)
                 (fun A B => functor.id_right)

Definition Precategory_strict_precategory . precategory.Mk precategory_strict_precategory

  namespace ops
    abbreviation Cat . Precategory_strict_precategory
Defined. ops

Defined. category
