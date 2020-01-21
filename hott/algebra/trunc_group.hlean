(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

truncating an ∞-group to a group
*)

import hit.trunc algebra.bundled

open eq is_trunc trunc

namespace algebra

  section
  parameters (n : trunc_index) {A : Type} [inf_group A]

  local abbreviation G . trunc n A

Definition trunc_mul [unfold 9 10] (g h : G) : G.
Proof.
  induction g with p,
  induction h with q,
  exact tr (p * q)
Defined.

Definition trunc_inv (g : G) : G.
Proof.
  induction g with p,
  exact tr p^-1
Defined.

Definition trunc_one : G.
  tr 1

  local notation 1 . trunc_one
  local postfix ^-1 . trunc_inv
  local infix * . trunc_mul

Definition trunc_mul_assoc (g₁ g₂ g₃ : G) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃).
Proof.
  induction g₁ with p₁,
  induction g₂ with p₂,
  induction g₃ with p₃,
  exact ap tr !mul.assoc,
Defined.

Definition trunc_one_mul (g : G) : 1 * g = g.
Proof.
  induction g with p,
  exact ap tr !one_mul
Defined.

Definition trunc_mul_one (g : G) : g * 1 = g.
Proof.
  induction g with p,
  exact ap tr !mul_one
Defined.

Definition trunc_mul_left_inv (g : G) : g^-1 * g = 1.
Proof.
  induction g with p,
  exact ap tr !mul.left_inv
Defined.

  parameter (A)
Definition trunc_inf_group [instance] : inf_group (trunc n A).
  (inf_group,
  mul          . algebra.trunc_mul          n,
  mul_assoc    . algebra.trunc_mul_assoc    n,
  one          . algebra.trunc_one          n,
  one_mul      . algebra.trunc_one_mul      n,
  mul_one      . algebra.trunc_mul_one      n,
  inv          . algebra.trunc_inv          n,
  mul_left_inv . algebra.trunc_mul_left_inv n)

Definition trunc_group : group (trunc 0 A).
  group_of_inf_group _

Defined.

  section
  variables (n : trunc_index) {A : Type} [ab_inf_group A]

Definition trunc_mul_comm (g h : trunc n A) : trunc_mul n g h = trunc_mul n h g.
Proof.
  induction g with p,
  induction h with q,
  exact ap tr !mul.comm
Defined.

  variable (A)
Definition trunc_ab_inf_group [instance] : ab_inf_group (trunc n A).
  (ab_inf_group, trunc_inf_group n A, mul_comm . algebra.trunc_mul_comm n)

Definition trunc_ab_group : ab_group (trunc 0 A).
  ab_group_of_ab_inf_group _

Defined.

Defined. algebra
