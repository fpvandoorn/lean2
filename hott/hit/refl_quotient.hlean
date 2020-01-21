(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Quotient of a reflexive relation
*)

import homotopy.circle cubical.squareover .two_quotient

open eq simple_two_quotient e_closure

namespace refl_quotient
section

  parameters {A : Type} (R : A -> A -> Type) (ρ : forall a, R a a)
  inductive refl_quotient_Q : forall (a : A), e_closure R a a -> Type.
  | Qmk {} : forall (a : A), refl_quotient_Q [ρ a]
  open refl_quotient_Q
  local abbreviation Q . refl_quotient_Q

Definition refl_quotient : Type . simple_two_quotient R Q

Definition rclass_of (a : A) : refl_quotient . incl0 R Q a
Definition req_of_rel (a a' : A) (r : R a a') : rclass_of a = rclass_of a'.
  incl1 R Q r

Definition pρ (a : A) : req_of_rel (ρ a) = idp.
  incl2 R Q (Qmk a)

  protectedDefinition rec {P : refl_quotient -> Type} (Pc : forall (a : A), P (rclass_of a))
  (Pp : forall (a a' : A) (H : R a a'), Pc a =[req_of_rel H] Pc a')
  (Pr : forall (a : A), change_path (pρ a) (Pp (ρ a)) = idpo) (x : refl_quotient) : P x.
Proof.
  induction x,
  exact Pc a,
  exact Pp s,
  induction q, apply Pr
Defined.

  protectedDefinition rec_on {P : refl_quotient -> Type} (x : refl_quotient)
  (Pc : forall (a : A), P (rclass_of a)) (Pp : forall (a a' : A) (H : R a a'), Pc a =[req_of_rel H] Pc a')
  (Pr : forall (a : A), change_path (pρ a) (Pp (ρ a)) = idpo) : P x.
  rec Pc Pp Pr x

Definition rec_req_of_rel {P : Type} {P : refl_quotient -> Type} (Pc : forall (a : A), P (rclass_of a))
  (Pp : forall (a a' : A) (H : R a a'), Pc a =[req_of_rel H] Pc a')
  (Pr : forall (a : A), change_path (pρ a) (Pp (ρ a)) = idpo) (a a' : A) (r : R a a')
  : apd (rec Pc Pp Pr) (req_of_rel r) = Pp r.
  !rec_incl1

  protectedDefinition elim {P : Type} (Pc : forall (a : A), P)
  (Pp : forall (a a' : A) (H : R a a'), Pc a = Pc a') (Pr : forall (a : A), Pp (ρ a) = idp)
  (x : refl_quotient) : P.
Proof.
  induction x,
  exact Pc a,
  exact Pp s,
  induction q, apply Pr
Defined.

  protectedDefinition elim_on {P : Type} (x : refl_quotient) (Pc : forall (a : A), P)
  (Pp : forall (a a' : A) (H : R a a'), Pc a = Pc a') (Pr : forall (a : A), Pp (ρ a) = idp) : P.
  elim Pc Pp Pr x

Definition elim_req_of_rel {P : Type} {Pc : forall (a : A), P}
  {Pp : forall (a a' : A) (H : R a a'), Pc a = Pc a'} (Pr : forall (a : A), Pp (ρ a) = idp)
  (a a' : A) (r : R a a') : ap (elim Pc Pp Pr) (req_of_rel r) = Pp r.
  !elim_incl1

Definition elim_pρ {P : Type} (Pc : forall (a : A), P)
  (Pp : forall (a a' : A) (H : R a a'), Pc a = Pc a') (Pr : forall (a : A), Pp (ρ a) = idp) (a : A)
  : square (ap02 (elim Pc Pp Pr) (pρ a)) (Pr a) (elim_req_of_rel Pr (ρ a)) idp.
  !elim_incl2

Defined.
Defined. refl_quotient



--attribute refl_quotient.elim_type [unfold 9]

--attribute refl_quotient.elim_type_on [unfold 6]
