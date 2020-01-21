(*
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jakob von Raumer

Categories of (hprop value) ordered sets.
*)
import ..category algebra.order types.fin

open algebra category is_trunc is_equiv equiv iso

namespace category

section
universe variable l
parameters (A : Type.{l}) [HA : is_set A] [OA : weak_order.{l} A]
  [Hle : forall a b : A, is_prop (a ≤ b)]
include A HA OA Hle

Definition precategory_order : precategory.{l l} A.
Proof.
  fconstructor,
  { intro a b, exact a ≤ b },
  { intro a b c, exact ge.trans },
  { intro a, apply le.refl },
  do 5 (intros; apply is_prop.elim),
  { intros, apply is_trunc_succ }
Defined.

local attribute [instance] precategory_order

Definition category_order : category.{l l} A.
Proof.
  fapply category.mk precategory_order,
  intros a b, fapply adjointify,
  { intro f, apply le.antisymm, apply iso.to_hom f, apply iso.to_inv f },
  { intro f, fapply iso_eq, esimp[precategory_order], apply is_prop.elim },
  { intro p, apply is_prop.elim }
Defined.

Defined.

Defined. category
