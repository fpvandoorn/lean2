(*
Copyright (c) 2018 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz
*)

import algebra.group_theory hit.set_quotient types.list homotopy.vankampen
       homotopy.susp .pushout ..algebra.free_group

open eq pointed equiv is_equiv is_trunc set_quotient sum list susp trunc algebra
     group pi pushout is_conn fiber unit function paths

namespace category
  open iso

Definition Groupoid_opposite (C : Groupoid) : Groupoid :=
  groupoid.MK (Opposite C) (fun x y f => @is_iso.mk _ (Opposite C) x y f
      (@is_iso.inverse _ C y x f ((@groupoid.all_iso _ C y x f)))
      (@is_iso.right_inverse _ C y x f ((@groupoid.all_iso _ C y x f)))
      (@is_iso.left_inverse _ C y x f ((@groupoid.all_iso _ C y x f))))

Definition hom_Group (C : Groupoid) (x : C) : Group :=
  Group.mk (hom x x) (hom_group x)

Definition fundamental_hom_group (A : pType) : hom_Group (Groupoid_opposite (forall ₁ A)) (Point A) <~>g forall ₁ A :=
Proof.
    fapply isomorphism_of_equiv,
    { reflexivity },
    { intros p q, reflexivity }
Defined.

Defined. category open category

Definition tr_trunc_eq (A : Type) (a : A) {x y : A} (p : x = y) (q : x = a)
  : transport (fun (z : A) => trunc 0 (z = a)) p (tr q) = tr (p^-1 @ q) :=
by induction p; induction q; reflexivity

namespace susp
  section
  universe variable u
  parameters (A : pType.{u}) [H : is_set A]
  include H

  local notation `F` := forall , star)

  local abbreviation C : Groupoid := Groupoid_bpushout (@id A) F F
  local abbreviation N : C := inl star
  local abbreviation S : C := inr star


Definition pglueNS (a : A) : hom N S :=
  class_of [ bpushout_prehom_index.DE (@id A) F F a ]

Definition pglueSN (a : A) : hom S N :=
  class_of [ bpushout_prehom_index.ED (@id A) F F a ]

Definition f : A \* hom N N -> hom S N :=
  prod.rec (fun a p => p o pglueSN a)

Definition g : A \* trunc 0 (@susp.north A = @susp.north A) -> trunc 0 (@susp.south A = @susp.north A) :=
  prod.rec (fun a p => tconcat (tr (merid a)^-1) p)

Definition foo : (Σ(z : susp A), trunc 0 (z = susp.north)) <~> pushout prod.pr2 g :=
Proof.
    apply equiv.trans !pushout.flattening',
    fapply pushout.equiv,
    { apply sigma.equiv_prod },
    { apply sigma.sigma_unit_left },
    { apply sigma.sigma_unit_left },
    { intro z, induction z with a p, induction p with p, reflexivity },
    { intro z, induction z with a p, induction p with p, apply tr_trunc_eq }
Defined.

Definition bar : pushout prod.pr2 g <~> pushout prod.pr2 f :=
Proof.
    fapply pushout.equiv,
    { apply prod.prod_equiv_prod_right, apply vankampen },
    { apply vankampen },
    { apply vankampen },
    { intro z, induction z with a p, reflexivity },
    { intro z, induction z with a p,
      change (encode (@id A) (fun (z : A) => star) (fun (z : A) => star) (tconcat (tr (merid a)^-1) p))
        = (encode (@id A) (fun (z : A) => star) (fun (z : A) => star) p o pglueSN a),
      revert p, fapply @trunc.rec 0 (@susp.north A = @susp.north A),
      { intro p, apply is_trunc_succ, apply is_trunc_eq, apply is_set_code }, intro p,
      apply trans (encode_tcon (@id A) (fun (z : A) => star) (fun (z : A) => star) (tr (merid a)^-1) (tr p)),
      apply ap (fun h => encode (@id A) (fun (z : A) => star) (fun (z : A) => star) (tr p) o h),
      apply encode_decode_singleton }
Defined.

Definition pfiber_susp_equiv_sigma : pfiber (ptr 1 (⅀ A)) <~> (Σ(z : susp A), trunc 0 (z = susp.north)) :=
Proof.
    apply equiv.trans !fiber.sigma_char,
    apply sigma.sigma_equiv_sigma_right,
    intro z, apply tr_eq_tr_equiv
Defined.

Definition is_trunc_susp_of_is_set : is_contr (Σ(z : susp A), trunc 0 (z = susp.north)) -> is_trunc 1 (susp A) :=
Proof.
    intro K,
    apply is_trunc_of_is_equiv_tr,
    apply is_equiv_of_is_contr_fun =>
    fapply @is_conn.elim -1 (ptrunc 1 (⅀ A)),
    exact is_contr_equiv_closed_rev pfiber_susp_equiv_sigma K
Defined.

Defined.

Defined. susp
