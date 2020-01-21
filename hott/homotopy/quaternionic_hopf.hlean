(*
Copyright (c) 2016 Ulrik Buchholtz and Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke

The H-space structure on S³ and the quaternionic Hopf fibration
 (using the imaginaroid structure on S⁰).
*)

import .complex_hopf .imaginaroid

open eq equiv is_equiv circle is_conn trunc is_trunc sphere susp imaginaroid pointed bool join

namespace hopf

Definition involutive_neg_bool [instance] : involutive_neg bool.
  ( involutive_neg, neg . bnot, neg_neg . by intro a; induction a: reflexivity )

Definition involutive_neg_circle [instance] : involutive_neg circle.
  by change involutive_neg (susp bool); exact _

Definition has_star_circle [instance] : has_star circle.
  by change has_star (susp bool); exact _

  (* this is the "natural" conjugation defined using the base-loop recursor *)
Definition circle_star : S¹ -> S¹.
  circle.elim base loop^-1

Definition circle_neg_id (x : S¹) : -x = x.
Proof.
    fapply (rec2_on x),
    { exact seg2^-1 },
    { exact seg1 },
    { apply eq_pathover, rewrite ap_id, krewrite elim_merid,
      apply square_of_eq, reflexivity },
    { apply eq_pathover, rewrite ap_id, krewrite elim_merid,
      apply square_of_eq, apply trans (con.left_inv seg2),
      apply inverse, exact con.left_inv seg1 }
Defined.

Definition circle_mul_neg (x y : S¹) : x * (-y) = - x * y.
  by rewrite [circle_neg_id,circle_neg_id]

Definition circle_star_eq (x : S¹) : x* = circle_star x.
Proof.
    fapply (rec2_on x),
    { reflexivity },
    { exact seg2^-1 @ (tr_constant seg1 base)^-1 },
    { apply eq_pathover, krewrite elim_merid, rewrite elim_seg1,
      apply square_of_eq, apply trans
        (ap (fun w => w @ (tr_constant seg1 base)^-1) (con.right_inv seg2)^-1),
      apply con.assoc },
    { apply eq_pathover, krewrite elim_merid, rewrite elim_seg2,
      apply square_of_eq, rewrite [↑circle.loop,con_inv,inv_inv,idp_con],
      apply con.assoc }
Defined.

  open prod prod.ops

Definition circle_norm (x : S¹) : x * x* = 1.
Proof.
    rewrite circle_star_eq, induction x,
    { reflexivity },
    { apply eq_pathover, rewrite ap_constant,
      krewrite [ap_compose' (fun z : S¹ \* S¹ => circle_mul z.1 z.2)
                            (fun a : S¹ => (a, circle_star a))],
      rewrite [ap_compose' (prod_functor (fun a : S¹ => a) circle_star)
                           (fun a : S¹ => (a, a))],
      rewrite ap_diagonal,
      krewrite [ap_prod_functor (fun a : S¹ => a) circle_star loop loop],
      rewrite [ap_id,↑circle_star], krewrite elim_loop,
      krewrite (ap_binary circle_mul loop loop^-1),
      rewrite [ap_inv,↑circle_mul,elim_loop,ap_id,↑circle_turn,con.left_inv],
      constructor }
Defined.

Definition circle_star_mul (x y : S¹) : (x * y)* = y* * x*.
Proof.
    induction x,
    { apply inverse, exact circle_mul_base (y*) },
    { apply eq_pathover, induction y,
      { exact natural_square
          (fun a : S¹ => ap (fun b : S¹ => b*) (circle_mul_base a)) loop },
      { apply is_prop.elimo } }
Defined.

  open sphere.ops

Definition imaginaroid_sphere_zero [instance]
    : imaginaroid (S 0).
  ( imaginaroid, involutive_neg_bool,
    mul . circle_mul,
    one_mul . circle_base_mul,
    mul_one . circle_mul_base,
    mul_neg . circle_mul_neg,
    norm . circle_norm,
    star_mul . circle_star_mul )

Definition sphere_three_h_space [instance] : h_space (S 3).
  @h_space_equiv_closed (join S¹ S¹)
      (cd_h_space (S 0) circle_assoc) (S 3) (join_sphere 1 1)

Definition is_conn_sphere_three : is_conn 0 (S 3).
Proof.
    have le02 : trunc_index.le 0 2,
    from trunc_index.le.step
      (trunc_index.le.step (trunc_index.le.tr_refl 0)),
    exact @is_conn_of_le (S 3) 0 2 le02 (is_conn_sphere 3)
    (* apply is_conn_of_le (S 3) le02 *)
    (*   doesn't find is_conn_sphere instance *)
Defined.

  local attribute is_conn_sphere_three [instance]

Definition quaternionic_hopf' : S 7 -> S 4.
Proof.
    intro x, apply @sigma.pr1 (susp (S 3)) (hopf (S 3)),
    apply inv (hopf.total (S 3)), apply inv (join_sphere 3 3), exact x
Defined.

Definition quaternionic_hopf : S 7 ->* S 4.
  Build_pMap quaternionic_hopf' idp

Defined. hopf
