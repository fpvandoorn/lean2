(*
Copyright (c) 2016 Ulrik Buchholtz and Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke, Floris van Doorn

The H-space structure on S¹ and the complex Hopf fibration
 (the standard one).
*)

import .hopf .circle types.fin

open eq equiv is_equiv circle is_conn trunc is_trunc sphere susp pointed fiber sphere.ops function
     join

namespace hopf

Definition circle_h_space [instance] : h_space S¹.
  ( h_space, one . base, mul . circle_mul,
    one_mul . circle_base_mul, mul_one . circle_mul_base )

Definition circle_assoc (x y z : S¹) : (x * y) * z = x * (y * z).
Proof.
    induction x,
    { reflexivity },
    { apply eq_pathover, induction y,
      { exact natural_square
          (fun a : S¹ => ap (fun b : S¹ => b * z) (circle_mul_base a))
          loop },
      { apply is_prop.elimo, apply is_trunc_square }}
Defined.

Definition complex_hopf' : S 3 -> S 2.
Proof.
    intro x, apply @sigma.pr1 (susp S¹) (hopf S¹),
    apply inv (hopf.total S¹), exact (join_sphere 1 1)^-1ᵉ x
Defined.

Definition complex_hopf : S 3 ->* S 2.
  proof Build_pMap complex_hopf' idp qed

Definition pfiber_complex_hopf : pfiber complex_hopf <~>* S 1.
Proof.
    fapply pequiv_of_equiv,
    { esimp, unfold [complex_hopf'],
      refine fiber.equiv_precompose (sigma.pr1 o (hopf.total S¹)^-1ᵉ)
        (join_sphere 1 1)^-1ᵉ _ @e _,
      refine fiber.equiv_precompose _ (hopf.total S¹)^-1ᵉ _ @e _,
      apply fiber_pr1 },
    { reflexivity }
Defined.

Defined. hopf
