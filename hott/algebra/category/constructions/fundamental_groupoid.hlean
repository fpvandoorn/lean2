(*
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn
*)

import ..groupoid ..functor.basic

open eq is_trunc iso trunc functor

namespace category

Definition fundamental_precategory (A : Type) : Precategory.
  precategory.MK A
                 (fun a a' => trunc 0 (a = a'))
                 _
                 (fun a₁ a₂ a₃ q p => tconcat p q)
                 (fun a => tidp)
                 (fun a₁ a₂ a₃ a₄ r q p => tassoc p q r)
                 (fun a₁ a₂ => tcon_tidp)
                 (fun a₁ a₂ => tidp_tcon)

Definition fundamental_groupoid (A : Type) : Groupoid.
  groupoid.MK (fundamental_precategory A)
              (fun a b p => is_iso.mk (tinverse p) (right_tinv p) (left_tinv p))

Definition fundamental_groupoid_functor {A B : Type} (f : A -> B) :
    fundamental_groupoid A ⇒ fundamental_groupoid B.
  functor.mk f (fun a a' => tap f) (fun a => tap_tidp f) (fun a₁ a₂ a₃ q p => tap_tcon f p q)

  notation `forall ₁` . fundamental_groupoid

  notation `forall ₁⇒` . fundamental_groupoid_functor

Defined. category
