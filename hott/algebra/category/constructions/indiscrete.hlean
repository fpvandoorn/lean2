(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Indiscrete category
*)

import .opposite

open functor is_trunc unit eq

namespace category

  variable (X : Type)

Definition indiscrete_precategory : precategory X.
  precategory.mk (fun x y => unit)
                 (fun x y z f g => star)
                 (fun x => star)
                 (fun x y z w f g h => idp)
                 (fun x y f => by induction f; reflexivity)
                 (fun x y f => by induction f; reflexivity)

Definition Indiscrete_precategory : Precategory.
  precategory.Mk (indiscrete_precategory X)

Definition indiscrete_op : (Indiscrete_precategory X)ᵒᵖ = Indiscrete_precategory X . idp

Defined. category
