(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the coequalizer
*)

import types.equiv .quotient

open quotient eq equiv is_trunc sigma sigma.ops

namespace coeq
section

universe u
parameters {A B : Type.{u}} (f g : A -> B)

  inductive coeq_rel : B -> B -> Type.
  | Rmk : forall (x : A), coeq_rel (f x) (g x)
  open coeq_rel
  local abbreviation R . coeq_rel

Definition coeq : Type . quotient coeq_rel (* TODO: define this in root namespace *)

Definition coeq_i (x : B) : coeq.
  class_of R x

  (* cp is the name Coq uses. I don't know what it abbreviates, but at least it's short :-) *)
Definition cp (x : A) : coeq_i (f x) = coeq_i (g x).
  eq_of_rel coeq_rel (Rmk f g x)

  protectedDefinition rec {P : coeq -> Type} (P_i : forall (x : B), P (coeq_i x))
  (Pcp : forall (x : A), P_i (f x) =[cp x] P_i (g x)) (y : coeq) : P y.
Proof.
  induction y,
  { apply P_i},
  { cases H, apply Pcp}
Defined.

  protectedDefinition rec_on {P : coeq -> Type} (y : coeq)
  (P_i : forall (x : B), P (coeq_i x)) (Pcp : forall (x : A), P_i (f x) =[cp x] P_i (g x)) : P y.
  rec P_i Pcp y

Definition rec_cp {P : coeq -> Type} (P_i : forall (x : B), P (coeq_i x))
  (Pcp : forall (x : A), P_i (f x) =[cp x] P_i (g x))
  (x : A) : apd (rec P_i Pcp) (cp x) = Pcp x.
  !rec_eq_of_rel

  protectedDefinition elim {P : Type} (P_i : B -> P)
  (Pcp : forall (x : A), P_i (f x) = P_i (g x)) (y : coeq) : P.
  rec P_i (fun x => pathover_of_eq _ (Pcp x)) y

  protectedDefinition elim_on {P : Type} (y : coeq) (P_i : B -> P)
  (Pcp : forall (x : A), P_i (f x) = P_i (g x)) : P.
  elim P_i Pcp y

Definition elim_cp {P : Type} (P_i : B -> P) (Pcp : forall (x : A), P_i (f x) = P_i (g x))
  (x : A) : ap (elim P_i Pcp) (cp x) = Pcp x.
Proof.
  apply eq_of_fn_eq_fn_inv !(pathover_constant (cp x)),
  rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim,rec_cp],
Defined.

  protectedDefinition elim_type (P_i : B -> Type)
  (Pcp : forall (x : A), P_i (f x) <~> P_i (g x)) (y : coeq) : Type.
  elim P_i (fun x => ua (Pcp x)) y

  protectedDefinition elim_type_on (y : coeq) (P_i : B -> Type)
  (Pcp : forall (x : A), P_i (f x) <~> P_i (g x)) : Type.
  elim_type P_i Pcp y

Definition elim_type_cp (P_i : B -> Type) (Pcp : forall (x : A), P_i (f x) <~> P_i (g x))
  (x : A) : transport (elim_type P_i Pcp) (cp x) = Pcp x.
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_cp];apply cast_ua_fn

  protectedDefinition rec_prop {P : coeq -> Type} [H : forall x, is_prop (P x)]
  (P_i : forall (x : B), P (coeq_i x)) (y : coeq) : P y.
  rec P_i (fun a => !is_prop.elimo) y

  protectedDefinition elim_prop {P : Type} [H : is_prop P] (P_i : B -> P) (y : coeq) : P.
  elim P_i (fun a => !is_prop.elim) y

Defined.

Defined. coeq







(* Flattening *)
namespace coeq
section
  open function

  universe u
  parameters {A B : Type.{u}} (f g : A -> B) (P_i : B -> Type)
  (Pcp : forall x : A, P_i (f x) <~> P_i (g x))

  local abbreviation P . coeq.elim_type f g P_i Pcp

  local abbreviation F : sigma (P_i o f) -> sigma P_i.
  fun z => ⟨f z.1, z.2⟩

  local abbreviation G : sigma (P_i o f) -> sigma P_i.
  fun z => ⟨g z.1, Pcp z.1 z.2⟩

  local abbreviation Pr : forall (b b' : B),
  coeq_rel f g b b' -> P_i b <~> P_i b'.
  @coeq_rel.rec A B f g _ Pcp

  local abbreviation P' . quotient.elim_type P_i Pr

  protectedDefinition flattening : sigma P <~> coeq F G.
Proof.
  have H : forall z, P z <~> P' z,
Proof.
  intro z, apply equiv_of_eq,
  have H1 : coeq.elim_type f g P_i Pcp = quotient.elim_type P_i Pr,
Proof.
  change
  quotient.rec P_i
  (fun b b' r => coeq_rel.cases_on r (fun x => pathover_of_eq _ (ua (Pcp x))))
  = quotient.rec P_i
  (fun b b' r => pathover_of_eq _ (ua (coeq_rel.cases_on r Pcp))),
  have H2 : forall (b b' : B) (r : coeq_rel f g b b'),
  coeq_rel.cases_on r (fun x => pathover_of_eq _ (ua (Pcp x)))
  = pathover_of_eq _ (ua (coeq_rel.cases_on r Pcp))
  :> P_i b =[eq_of_rel (coeq_rel f g) r] P_i b',
Proof. intros b b' r, cases r, reflexivity end,
  rewrite (eq_of_homotopy3 H2)
Defined.,
  apply ap10 H1
Defined.,
  apply equiv.trans (sigma_equiv_sigma_right H),
  apply equiv.trans !quotient.flattening.flattening_lemma,
  fapply quotient.equiv,
  { reflexivity },
  { intros bp bp',
  fapply equiv.MK,
  { intro r, induction r with b b' r p,
  induction r with x, exact coeq_rel.Rmk F G ⟨x, p⟩ },
  { esimp, intro r, induction r with xp,
  induction xp with x p,
  exact quotient.flattening.flattening_rel.mk Pr
  (coeq_rel.Rmk f g x) p },
  { esimp, intro r, induction r with xp,
  induction xp with x p, reflexivity },
  { intro r, induction r with b b' r p,
  induction r with x, reflexivity } }
Defined.
Defined.
Defined. coeq
