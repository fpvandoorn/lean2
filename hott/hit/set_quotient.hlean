(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of set-quotients, i.e. quotient of a mere relation which is then set-truncated.
*)

import function algebra.relation types.trunc types.eq hit.quotient

open eq is_trunc trunc quotient equiv is_equiv

namespace set_quotient
section
  parameters {A : Type} (R : A -> A -> Prop)
  (* set-quotients are just set-truncations of (type) quotients *)
Definition set_quotient : Type . trunc 0 (quotient R)

  parameter {R}
Definition class_of (a : A) : set_quotient.
  tr (class_of _ a)

Definition eq_of_rel {a a' : A} (H : R a a') : class_of a = class_of a'.
  ap tr (eq_of_rel _ H)

Definition is_set_set_quotient [instance] : is_set set_quotient.
Proof. unfold set_quotient, exact _ end

  protectedDefinition rec {P : set_quotient -> Type} [Pt : forall aa, is_set (P aa)]
  (Pc : forall (a : A), P (class_of a)) (Pp : forall (a a' : A) (H : R a a'), Pc a =[eq_of_rel H] Pc a')
  (x : set_quotient) : P x.
Proof.
  apply (@trunc.rec_on _ _ P x),
  { intro x', apply Pt},
  { intro y, induction y,
  { apply Pc},
  { exact pathover_of_pathover_ap P tr (Pp H)}}
Defined.

  protectedDefinition rec_on {P : set_quotient -> Type} (x : set_quotient)
  [Pt : forall aa, is_set (P aa)] (Pc : forall (a : A), P (class_of a))
  (Pp : forall (a a' : A) (H : R a a'), Pc a =[eq_of_rel H] Pc a') : P x.
  rec Pc Pp x

Definition rec_eq_of_rel {P : set_quotient -> Type} [Pt : forall aa, is_set (P aa)]
  (Pc : forall (a : A), P (class_of a)) (Pp : forall (a a' : A) (H : R a a'), Pc a =[eq_of_rel H] Pc a')
  {a a' : A} (H : R a a') : apd (rec Pc Pp) (eq_of_rel H) = Pp H.
  !is_set.elimo

  protectedDefinition elim {P : Type} [Pt : is_set P] (Pc : A -> P)
  (Pp : forall (a a' : A) (H : R a a'), Pc a = Pc a') (x : set_quotient) : P.
  rec Pc (fun a a' H => pathover_of_eq _ (Pp H)) x

  protectedDefinition elim_on {P : Type} (x : set_quotient) [Pt : is_set P]
  (Pc : A -> P) (Pp : forall (a a' : A) (H : R a a'), Pc a = Pc a')  : P.
  elim Pc Pp x

Definition elim_eq_of_rel {P : Type} [Pt : is_set P] (Pc : A -> P)
  (Pp : forall (a a' : A) (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
  : ap (elim Pc Pp) (eq_of_rel H) = Pp H.
Proof.
  apply eq_of_fn_eq_fn_inv !(pathover_constant (eq_of_rel H)),
  rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim,rec_eq_of_rel],
Defined.

  protectedDefinition rec_prop {P : set_quotient -> Type} [Pt : forall aa, is_prop (P aa)]
  (Pc : forall (a : A), P (class_of a)) (x : set_quotient) : P x.
  rec Pc (fun a a' H => !is_prop.elimo) x

  protectedDefinition elim_prop {P : Type} [Pt : is_prop P] (Pc : A -> P) (x : set_quotient)
  : P.
  elim Pc (fun a a' H => !is_prop.elim) x

Defined.
Defined. set_quotient





open sigma relation function

namespace set_quotient
  variables {A B C : Type} (R : A -> A -> Prop) (S : B -> B -> Prop) (T : C -> C -> Prop)

Definition is_surjective_class_of : is_surjective (class_of : A -> set_quotient R).
  fun x => set_quotient.rec_on x (fun a => tr (fiber.mk a idp)) (fun a a' r => !is_prop.elimo)

Definition is_prop_set_quotient {A : Type} (R : A -> A -> Prop) [is_prop A] :
  is_prop (set_quotient R).
Proof.
  apply is_prop.mk, intro x y,
  induction x using set_quotient.rec_prop, induction y using set_quotient.rec_prop,
  exact ap class_of !is_prop.elim
Defined.

  local attribute is_prop_set_quotient [instance]
Definition is_trunc_set_quotient [instance] (n : ℕ₋₂) {A : Type} (R : A -> A -> Prop) [is_trunc n A] :
  is_trunc n (set_quotient R).
Proof.
  cases n with n, { apply is_contr_of_inhabited_prop, exact class_of !center },
  cases n with n, { apply _ },
  apply is_trunc_succ_succ_of_is_set
Defined.

Definition is_equiv_class_of {A : Type} [is_set A] (R : A -> A -> Prop)
  (p : forall (a b), R a b -> a = b) : is_equiv (@class_of A R).
Proof.
  fapply adjointify,
  { intro x, induction x, exact a, exact p H },
  { intro x, induction x using set_quotient.rec_prop, reflexivity },
  { intro a, reflexivity }
Defined.

Definition equiv_set_quotient {A : Type} [is_set A] (R : A -> A -> Prop)
  (p : forall (a b), R a b -> a = b) : A <~> set_quotient R.
  equiv.mk _ (is_equiv_class_of R p)

  (* non-dependent universal property *)

Definition set_quotient_arrow_equiv (B : Type) [H : is_set B] :
  (set_quotient R -> B) <~> (Σ(f : A -> B), forall (a a' : A), R a a' -> f a = f a').
Proof.
  fapply equiv.MK,
  { intro f, exact ⟨fun a => f (class_of a), fun a a' r => ap f (eq_of_rel r)⟩},
  { intro v x, induction v with f p, exact set_quotient.elim_on x f p},
  { intro v, induction v with f p, esimp, apply ap (sigma.mk f),
  apply eq_of_homotopy3, intro a a' r, apply elim_eq_of_rel},
  { intro f, apply eq_of_homotopy, intro x, refine set_quotient.rec_on x _ _: esimp,
  intro a, reflexivity,
  intro a a' r, apply eq_pathover, apply hdeg_square, apply elim_eq_of_rel}
Defined.

  protectedDefinition code (a : A) (x : set_quotient R) [H : is_equivalence R]
  : Prop.
  set_quotient.elim_on x (R a)
Proof.
  intros a' a'' H1,
  refine to_inv !trunctype_eq_equiv _, esimp,
  apply ua,
  apply equiv_of_is_prop,
  { intro H2, exact is_transitive.trans R H2 H1},
  { intro H2, apply is_transitive.trans R H2, exact is_symmetric.symm R H1}
Defined.

  protectedDefinition encode {a : A} {x : set_quotient R} (p : class_of a = x)
  [H : is_equivalence R] : set_quotient.code R a x.
Proof.
  induction p, esimp, apply is_reflexive.refl R
Defined.

Definition rel_of_eq {a a' : A} (p : class_of a = class_of a' :> set_quotient R)
  [H : is_equivalence R] : R a a'.
  set_quotient.encode R p

  variables {R S T}
Definition quotient_unary_map (f : A -> B) (H : forall {a a'} (r : R a a'), S (f a) (f a')) :
  set_quotient R -> set_quotient S.
  set_quotient.elim (class_of o f) (fun a a' r => eq_of_rel (H r))

Definition quotient_binary_map [unfold 11 12] (f : A -> B -> C)
  (H : forall {a a'} (r : R a a') {b b'} (s : S b b'), T (f a b) (f a' b'))
  [HR : is_reflexive R] [HS : is_reflexive S] :
  set_quotient R -> set_quotient S -> set_quotient T.
Proof.
  refine set_quotient.elim _ _,
  { intro a, refine set_quotient.elim _ _,
  { intro b, exact class_of (f a b)},
  { intro b b' s, apply eq_of_rel, apply H, apply is_reflexive.refl R, exact s}},
  { intro a a' r, apply eq_of_homotopy, refine set_quotient.rec _ _,
  { intro b, esimp, apply eq_of_rel, apply H, exact r, apply is_reflexive.refl S},
  { intro b b' s, apply eq_pathover, esimp, apply is_set.elims}}
Defined.

Defined. set_quotient
