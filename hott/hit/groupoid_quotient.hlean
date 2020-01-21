(*
Copyright (c) 2015-16 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

The groupoid quotient. This is a 1-type which path spaces is the same as the morphisms
a given groupoid. We define it as the 1-truncation of a two quotient.
*)

import algebra.category.groupoid .two_quotient homotopy.connectedness
  algebra.group_theory

open trunc_two_quotient eq bool unit relation category e_closure iso is_trunc trunc equiv is_equiv
  group

namespace groupoid_quotient
section
  parameter (G : Groupoid)

  inductive groupoid_quotient_R : G -> G -> Type.
  | Rmk : forall {a b : G} (f : a ⟶ b), groupoid_quotient_R a b

  open groupoid_quotient_R
  local abbreviation R . groupoid_quotient_R

  inductive groupoid_quotient_Q : forall (x y : G),
  e_closure groupoid_quotient_R x y -> e_closure groupoid_quotient_R x y -> Type.
  | Qconcat : forall {a b c : G} (g : b ⟶ c) (f : a ⟶ b),
  groupoid_quotient_Q [Rmk (g o f)] ([Rmk f] @r [Rmk g])

  open groupoid_quotient_Q
  local abbreviation Q . groupoid_quotient_Q

Definition groupoid_quotient . trunc_two_quotient 1 R Q

  local attribute groupoid_quotient [reducible]
Definition is_trunc_groupoid_quotient [instance] : is_trunc 1 groupoid_quotient . _

  parameter {G}
  variables {a b c : G}
Definition elt (a : G) : groupoid_quotient . incl0 a
Definition pth (f : a ⟶ b) : elt a = elt b . incl1 (Rmk f)
Definition resp_comp (g : b ⟶ c) (f : a ⟶ b) : pth (g o f) = pth f @ pth g . incl2 (Qconcat g f)
Definition resp_id (a : G) : pth (ID a) = idp.
Proof.
  apply cancel_right (pth (id)), refine _ @ (concat_1p _)^-1,
  refine !resp_comp^-1 @ _,
  exact ap pth !id_id,
Defined.

Definition resp_inv (f : a ⟶ b) : pth (f^-1) = (pth f)^-1.
Proof.
  apply eq_inv_of_con_eq_idp',
  refine !resp_comp^-1 @ _,
  refine ap pth !right_inverse @ _,
  apply resp_id
Defined.

  protectedDefinition rec {P : groupoid_quotient -> Type} [forall x, is_trunc 1 (P x)]
  (Pe : forall g, P (elt g)) (Pp : forall (a b) (f : a ⟶ b), Pe a =[pth f] Pe b)
  (Pcomp : forall (a b c) (g : b ⟶ c) (f : a ⟶ b),
  change_path (resp_comp g f) (Pp (g o f)) = Pp f @o Pp g)
  (x : groupoid_quotient) : P x.
Proof.
  induction x,
  { apply Pe},
  { induction s with a b f, apply Pp},
  { induction q with a b c g f,
  apply Pcomp}
Defined.

  protectedDefinition rec_on {P : groupoid_quotient -> Type} [forall x, is_trunc 1 (P x)]
  (x : groupoid_quotient)
  (Pe : forall g, P (elt g)) (Pp : forall (a b) (f : a ⟶ b), Pe a =[pth f] Pe b)
  (Pcomp : forall (a b c) (g : b ⟶ c) (f : a ⟶ b),
  change_path (resp_comp g f) (Pp (g o f)) = Pp f @o Pp g) : P x.
  rec Pe Pp Pcomp x

  protectedDefinition set_rec {P : groupoid_quotient -> Type} [forall x, is_set (P x)]
  (Pe : forall g, P (elt g)) (Pp : forall (a b) (f : a ⟶ b), Pe a =[pth f] Pe b)
  (x : groupoid_quotient) : P x.
  rec Pe Pp !center x

  protectedDefinition prop_rec {P : groupoid_quotient -> Type} [forall x, is_prop (P x)]
  (Pe : forall g, P (elt g)) (x : groupoid_quotient) : P x.
  rec Pe !center !center x

Definition rec_pth {P : groupoid_quotient -> Type} [forall x, is_trunc 1 (P x)]
  {Pe : forall g, P (elt g)} {Pp : forall (a b) (f : a ⟶ b), Pe a =[pth f] Pe b}
  (Pcomp : forall (a b c) (g : b ⟶ c) (f : a ⟶ b),
  change_path (resp_comp g f) (Pp (g o f)) = Pp f @o Pp g)
  {a b : G} (f : a ⟶ b) : apd (rec Pe Pp Pcomp) (pth f) = Pp f.
  proof !rec_incl1 qed

  protectedDefinition elim {P : Type} [is_trunc 1 P] (Pe : G -> P)
  (Pp : forall (a b) (f : a ⟶ b), Pe a = Pe b)
  (Pcomp : forall (a b c) (g : b ⟶ c) (f : a ⟶ b), Pp (g o f) = Pp f @ Pp g)
  (x : groupoid_quotient) : P.
Proof.
  induction x,
  { exact Pe a},
  { induction s with a b f, exact Pp f},
  { induction q with a b c g f,
  exact Pcomp g f}
Defined.

  protectedDefinition elim_on {P : Type} [is_trunc 1 P] (x : groupoid_quotient)
  (Pe : G -> P) (Pp : forall (a b) (f : a ⟶ b), Pe a = Pe b)
  (Pcomp : forall (a b c) (g : b ⟶ c) (f : a ⟶ b), Pp (g o f) = Pp f @ Pp g) : P.
  elim Pe Pp Pcomp x

  protectedDefinition set_elim {P : Type} [is_set P] (Pe : G -> P)
  (Pp : forall (a b) (f : a ⟶ b), Pe a = Pe b)
  (x : groupoid_quotient) : P.
  elim Pe Pp !center x

  protectedDefinition prop_elim {P : Type} [is_prop P] (Pe : G -> P)
  (x : groupoid_quotient) : P.
  elim Pe !center !center x

Definition elim_pth {P : Type} [is_trunc 1 P] {Pe : G -> P} {Pp : forall (a b) (f : a ⟶ b), Pe a = Pe b}
  (Pcomp : forall (a b c) (g : b ⟶ c) (f : a ⟶ b), Pp (g o f) = Pp f @ Pp g) {a b : G} (f : a ⟶ b) :
  ap (elim Pe Pp Pcomp) (pth f) = Pp f.
  !elim_incl1

  (* The following rule is also true because P is a 1-type, and can be proven by `!is_set.elims` *)
  (* The following is the canonical proofs which holds for any truncated two-quotient. *)
Definition elim_resp_comp {P : Type} [is_trunc 1 P] {Pe : G -> P}
  {Pp : forall (a b) (f : a ⟶ b), Pe a = Pe b}
  (Pcomp : forall (a b c) (g : b ⟶ c) (f : a ⟶ b), Pp (g o f) = Pp f @ Pp g)
  {a b c : G} (g : b ⟶ c) (f : a ⟶ b)
  : square (ap02 (elim Pe Pp Pcomp) (resp_comp g f))
  (Pcomp g f)
  (elim_pth Pcomp (g o f))
  ((ap_pp _ _ _) @ (elim_pth Pcomp f ◾ elim_pth Pcomp g)).
  proof !elim_incl2 qed

  protectedDefinition elim_set.{u} (Pe : G -> Set.{u}) (Pp : forall (a b) (f : a ⟶ b), Pe a <~> Pe b)
  (Pcomp : forall (a b c) (g : b ⟶ c) (f : a ⟶ b) (x : Pe a), Pp (g o f) x = Pp g (Pp f x))
  (x : groupoid_quotient) : Set.{u}.
  elim Pe (fun a b f => tua (Pp f)) (fun a b c g f => ap tua (equiv_eq (Pcomp g f)) @ !tua_trans) x

Definition elim_set_pth {Pe : G -> Set} {Pp : forall (a b) (f : a ⟶ b), Pe a <~> Pe b}
  (Pcomp : forall (a b c) (g : b ⟶ c) (f : a ⟶ b) (x : Pe a), Pp (g o f) x = Pp g (Pp f x))
  {a b : G} (f : a ⟶ b) :
  transport (elim_set Pe Pp Pcomp) (pth f) = Pp f.
  by rewrite [tr_eq_cast_ap_fn, ↑elim_set, ▸*, ap_compose' trunctype.carrier, elim_pth];
  apply tcast_tua_fn

Defined.
Defined. groupoid_quotient






  groupoid_quotient.elim_set [unfold 5]


open sigma pi is_conn function
namespace groupoid_quotient
section
  universe variables u v
  variables {G : Groupoid.{u v}} (a : G) {b c : G}

  include a

  protectedDefinition code (x : groupoid_quotient G) : Set.{v}.
Proof.
  refine groupoid_quotient.elim_set _ _ _ x,
  { intro b, exact homset a b},
  { intro b c g, exact equiv_postcompose g},
  { intro b c d h g f, esimp at *, apply assoc'}
Defined.

  omit a

  local abbreviation code . @groupoid_quotient.code G a

  variable {a}
  protectedDefinition encode (x : groupoid_quotient G) (p : elt a = x) : code a x.
  transport (code a) p (ID a)

  protectedDefinition decode (x : groupoid_quotient G) (z : code a x) : elt a = x.
Proof.
  induction x using groupoid_quotient.set_rec with b b c g,
  { esimp, exact pth z},
  { apply arrow_pathover_left, esimp, intro f, apply eq_pathover_constant_left_id_right,
  apply square_of_eq, refine !resp_comp^-1 @ _ @ (concat_1p _)^-1, rewrite elim_set_pth}
Defined.

  local abbreviation encode [unfold_full] . @groupoid_quotient.encode G a
  local abbreviation decode [unfold_full] . @groupoid_quotient.decode G a

  protectedDefinition decode_encode (x : groupoid_quotient G) (p : elt a = x) :
  decode x (encode x p) = p.
Proof. induction p, esimp, apply resp_id end

  protectedDefinition encode_decode (x : groupoid_quotient G) (z : code a x) :
  encode x (decode x z) = z.
Proof.
  induction x using groupoid_quotient.prop_rec with b,
  esimp, refine ap10 !elim_set_pth.{u v v} (ID a) @ _, esimp,
  apply id_right
Defined.

Definition decode_comp (z : code a (elt b)) (z' : code b (elt c)) :
  decode (elt c) (z' o z) = decode (elt b) z @ decode (elt c) z'.
  !resp_comp

  variables (a b)
Definition elt_eq_elt_equiv : (elt a = elt b) <~> (a ⟶ b).
  equiv.MK (encode (elt b)) (decode (elt b))
  (groupoid_quotient.encode_decode (elt b)) (groupoid_quotient.decode_encode (elt b))

  variables {a b}
Definition encode_con (p : elt a = elt b)
  (q : elt b = elt c) : encode (elt c) (p @ q) = encode (elt c) q o encode (elt b) p.
Proof.
  apply eq_of_fn_eq_fn (elt_eq_elt_equiv a c)^-1ᵉ,
  refine !right_inv @ _ @ !decode_comp^-1,
  apply concat2, do 2 exact (to_left_inv !elt_eq_elt_equiv _)^-1
Defined.

  variable (G)
Definition is_conn_groupoid_quotient [H : is_conn 0 G] : is_conn 0 (groupoid_quotient G).
Proof.
  have g : trunc 0 G, from !center,
  induction g with g,
  have p : forall h, ∥ g = h ∥,
Proof.
  intro h, refine !tr_eq_tr_equiv _, apply is_prop.elim
Defined.,
  fapply is_contr.mk,
  { apply trunc_functor 0 elt (tr g)} =>
  { intro x, induction x with x,
  induction x using groupoid_quotient.prop_rec with b, esimp,
  induction p b with q, exact ap (tr o elt) q}
Defined.

Defined.

Defined. groupoid_quotient

export [unfold] groupoid_quotient
