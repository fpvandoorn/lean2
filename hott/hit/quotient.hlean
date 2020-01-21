(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz

Quotients. This is a quotient without truncation for an arbitrary type-valued binary relation.
See also .set_quotient
*)

(*
  The hit quotient is primitive, declared in init.hit.
  The constructors are, given {A : Type} (R : A -> A -> Type),
  * class_of : A -> quotient R (A implicit, R explicit)
  * eq_of_rel : forall {a a' : A}, R a a' -> class_of a = class_of a' (R explicit)
*)

import arity cubical.squareover types.arrow cubical.pathover2 types.pointed

open eq equiv sigma sigma.ops pi is_trunc pointed

namespace quotient

  variables {A : Type} {R : A -> A -> Type}

  protectedDefinition elim {P : Type} (Pc : A -> P) (Pp : forall (a a' : A) (H : R a a'), Pc a = Pc a')
  (x : quotient R) : P.
  quotient.rec Pc (fun a a' H => pathover_of_eq _ (Pp H)) x

  protectedDefinition elim_on {P : Type} (x : quotient R)
  (Pc : A -> P) (Pp : forall (a a' : A) (H : R a a'), Pc a = Pc a') : P.
  quotient.elim Pc Pp x

Definition elim_eq_of_rel {P : Type} (Pc : A -> P)
  (Pp : forall (a a' : A) (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
  : ap (quotient.elim Pc Pp) (eq_of_rel R H) = Pp H.
Proof.
  apply eq_of_fn_eq_fn_inv !(pathover_constant (eq_of_rel R H)),
  rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑quotient.elim,rec_eq_of_rel],
Defined.

  protectedDefinition rec_prop {A : Type} {R : A -> A -> Type} {P : quotient R -> Type}
  [H : forall x, is_prop (P x)] (Pc : forall (a : A), P (class_of R a)) (x : quotient R) : P x.
  quotient.rec Pc (fun a a' H => !is_prop.elimo) x

  protectedDefinition elim_prop {P : Type} [H : is_prop P] (Pc : A -> P) (x : quotient R) : P.
  quotient.elim Pc (fun a a' H => !is_prop.elim) x

  protectedDefinition elim_type (Pc : A -> Type)
  (Pp : forall (a a' : A) (H : R a a'), Pc a <~> Pc a') : quotient R -> Type.
  quotient.elim Pc (fun a a' H => ua (Pp H))

  protectedDefinition elim_type_on (x : quotient R) (Pc : A -> Type)
  (Pp : forall (a a' : A) (H : R a a'), Pc a <~> Pc a') : Type.
  quotient.elim_type Pc Pp x

Definition elim_type_eq_of_rel_fn (Pc : A -> Type)
  (Pp : forall (a a' : A) (H : R a a'), Pc a <~> Pc a') {a a' : A} (H : R a a')
  : transport (quotient.elim_type Pc Pp) (eq_of_rel R H) = to_fun (Pp H).
  by rewrite [tr_eq_cast_ap_fn, ↑quotient.elim_type, elim_eq_of_rel]; apply cast_ua_fn

  (* rename to elim_type_eq_of_rel_fn_inv *)
Definition elim_type_eq_of_rel_inv (Pc : A -> Type)
  (Pp : forall (a a' : A) (H : R a a'), Pc a <~> Pc a') {a a' : A} (H : R a a')
  : transport (quotient.elim_type Pc Pp) (eq_of_rel R H)^-1 = to_inv (Pp H).
  by rewrite [tr_eq_cast_ap_fn, ↑quotient.elim_type, ap_inv, elim_eq_of_rel]; apply cast_ua_inv_fn

  (* remove ' *)
Definition elim_type_eq_of_rel_inv' (Pc : A -> Type)
  (Pp : forall (a a' : A) (H : R a a'), Pc a <~> Pc a') {a a' : A} (H : R a a') (x : Pc a')
  : transport (quotient.elim_type Pc Pp) (eq_of_rel R H)^-1 x = to_inv (Pp H) x.
  ap10 (elim_type_eq_of_rel_inv Pc Pp H) x

Definition elim_type_eq_of_rel.{u} (Pc : A -> Type.{u})
  (Pp : forall (a a' : A) (H : R a a'), Pc a <~> Pc a') {a a' : A} (H : R a a') (p : Pc a)
  : transport (quotient.elim_type Pc Pp) (eq_of_rel R H) p = to_fun (Pp H) p.
  ap10 (elim_type_eq_of_rel_fn Pc Pp H) p

Definition elim_type_eq_of_rel' (Pc : A -> Type)
  (Pp : forall (a a' : A) (H : R a a'), Pc a <~> Pc a') {a a' : A} (H : R a a') (p : Pc a)
  : pathover (quotient.elim_type Pc Pp) p (eq_of_rel R H) (to_fun (Pp H) p).
  pathover_of_tr_eq (elim_type_eq_of_rel Pc Pp H p)

Definition elim_type_uncurried (H : Σ(Pc : A -> Type),  forall (a a' : A) (H : R a a'), Pc a <~> Pc a')
  : quotient R -> Type.
  quotient.elim_type H.1 H.2
Defined. quotient







namespace quotient

  section
  variables {A : Type} (R : A -> A -> Type)

  (* The dependent universal property *)
Definition quotient_pi_equiv (C : quotient R -> Type) : (forall x, C x) <~>
  (Σ(f : forall (a : A), C (class_of R a)),  forall (a a' : A) (H : R a a'), f a =[eq_of_rel R H] f a').
Proof.
  fapply equiv.MK,
  { intro f, exact ⟨fun a => f (class_of R a), fun a a' H => apd f (eq_of_rel R H)⟩},
  { intro v x, induction v with i p, induction x,
  exact (i a),
  exact (p H)},
  { intro v, induction v with i p, esimp,
  apply ap (sigma.mk i), apply eq_of_homotopy3, intro a a' H, apply rec_eq_of_rel},
  { intro f, apply eq_of_homotopy, intro x, induction x: esimp,
  apply eq_pathover_dep, esimp, rewrite rec_eq_of_rel, exact hrflo},
Defined.
Defined.

Definition pquotient {A : pType} (R : A -> A -> Type) : pType.
  Build_pType (quotient R) (class_of R (point _))

  (* the flattening lemma *)

  namespace flattening
  section

  parameters {A : Type} (R : A -> A -> Type) (C : A -> Type) (f : forall (a a'), R a a' -> C a <~> C a')
  include f
  variables {a a' : A} {r : R a a'}

  local abbreviation P . quotient.elim_type C f

Definition flattening_type : Type . Σa, C a
  local abbreviation X . flattening_type
  inductive flattening_rel : X -> X -> Type.
  | mk : forall (a a' : A) (r : R a a') (c : C a), flattening_rel ⟨a, c⟩ ⟨a', f r c⟩

Definition Ppt (c : C a) : sigma P.
  ⟨class_of R a, c⟩

Definition Peq (r : R a a') (c : C a) : Ppt c = Ppt (f r c).
Proof.
  fapply sigma_eq: esimp,
  { apply eq_of_rel R r},
  { refine elim_type_eq_of_rel' C f r c}
Defined.

Definition rec {Q : sigma P -> Type} (Qpt : forall {a : A} (x : C a), Q (Ppt x))
  (Qeq : forall (a a' : A) (r : R a a') (c : C a), Qpt c =[Peq r c] Qpt (f r c))
  (v : sigma P) : Q v.
Proof.
  induction v with q p,
  induction q,
  { exact Qpt p},
  { apply pi_pathover_left', esimp, intro c,
  refine _ @op apdt Qpt (elim_type_eq_of_rel C f H c)^-1ᵖ,
  refine _ @op (tr_compose Q Ppt _ _)^-1 ,
  rewrite ap_inv,
  refine pathover_cancel_right _ !tr_pathover^-1ᵒ,
  refine change_path _ (Qeq H c),
  symmetry, rewrite [↑[Ppt, Peq]],
  refine whisker_left _ !ap_dpair @ _,
  refine !dpair_eq_dpair_con^-1 @ _, esimp,
  apply ap (dpair_eq_dpair _),
  esimp [elim_type_eq_of_rel',pathover_idp_of_eq],
  exact !pathover_of_tr_eq_eq_concato^-1},
Defined.

Definition elim {Q : Type} (Qpt : forall {a : A}, C a -> Q)
  (Qeq : forall (a a' : A) (r : R a a') (c : C a), Qpt c = Qpt (f r c))
  (v : sigma P) : Q.
Proof.
  induction v with q p,
  induction q,
  { exact Qpt p},
  { apply arrow_pathover_constant_right, esimp,
  intro c, exact Qeq H c @ ap Qpt (elim_type_eq_of_rel C f H c)^-1},
Defined.

Definition elim_Peq {Q : Type} (Qpt : forall {a : A}, C a -> Q)
  (Qeq : forall (a a' : A) (r : R a a') (c : C a), Qpt c = Qpt (f r c)) {a a' : A} (r : R a a')
  (c : C a) : ap (elim @Qpt Qeq) (Peq r c) = Qeq r c.
Proof.
  refine !ap_dpair_eq_dpair @ _,
  refine !apd011_eq_apo11_apd @ _,
  rewrite [rec_eq_of_rel, ▸*],
  refine !apo11_arrow_pathover_constant_right @ _,
  rewrite [↑elim_type_eq_of_rel', to_right_inv !pathover_equiv_tr_eq, ap_inv],
  apply inv_con_cancel_right
Defined.

  open flattening_rel
Definition flattening_lemma : sigma P <~> quotient flattening_rel.
Proof.
  fapply equiv.MK,
  { refine elim _ _,
  { intro a c, exact class_of _ ⟨a, c⟩},
  { intro a a' r c, apply eq_of_rel, constructor}},
  { intro q, induction q with x x x' H,
  { exact Ppt x.2},
  { induction H, esimp, apply Peq}},
  { intro q, induction q with x x x' H: esimp,
  { induction x with a c, reflexivity},
  { induction H, esimp, apply eq_pathover, apply hdeg_square,
  refine ap_compose (elim _ _) (quotient.elim _ _) _ @ _,
  rewrite [elim_eq_of_rel, ap_id, ▸*],
  apply elim_Peq}},
  { refine rec (fun a x => idp) _, intros,
  apply eq_pathover, apply hdeg_square,
  refine ap_compose (quotient.elim _ _) (elim _ _) _ @ _,
  rewrite [elim_Peq, ap_id, ▸*],
  apply elim_eq_of_rel}
Defined.

Defined.
Defined. flattening

  section
  open is_equiv equiv prod prod.ops
  variables {A : Type} (R : A -> A -> Type)
  {B : Type} (Q : B -> B -> Type)
  (f : A -> B) (k : forall a a' : A, R a a' -> Q (f a) (f a'))
  include f k

  protectedDefinition functor : quotient R -> quotient Q.
  quotient.elim (fun a => class_of Q (f a)) (fun a a' r => eq_of_rel Q (k a a' r))

  variables [F : is_equiv f] [K : forall a a', is_equiv (k a a')]
  include F K

  protectedDefinition functor_inv : quotient Q -> quotient R.
  quotient.elim (fun b => class_of R (f^-1 b))
  (fun b b' q => eq_of_rel R ((k (f^-1 b) (f^-1 b'))^-1
  ((right_inv f b)^-1 # (right_inv f b')^-1 # q)))

  protectedDefinition is_equiv [instance]
  : is_equiv (quotient.functor R Q f k).
Proof.
  fapply adjointify _ (quotient.functor_inv R Q f k) =>
  { intro qb, induction qb with b b b' q,
  { apply ap (class_of Q), apply right_inv },
  { apply eq_pathover, rewrite [ap_id,ap_compose' (quotient.elim _ _)],
  do 2 krewrite elim_eq_of_rel, rewrite (right_inv (k (f^-1 b) (f^-1 b'))),
  have H1 : pathover (fun z : B \* B => Q z.1 z.2)
  ((right_inv f b)^-1 # (right_inv f b')^-1 # q)
  (prod_eq (right_inv f b) (right_inv f b')) q,
Proof. apply pathover_of_eq_tr, krewrite [prod_eq_inv,prod_eq_transport] end,
  have H2 : square
  (ap (fun x : (Σz : B \* B => Q z.1 z.2), class_of Q x.1.1)
  (sigma_eq (prod_eq (right_inv f b) (right_inv f b')) H1))
  (ap (fun x : (Σz : B \* B => Q z.1 z.2), class_of Q x.1.2)
  (sigma_eq (prod_eq (right_inv f b) (right_inv f b')) H1))
  (eq_of_rel Q ((right_inv f b)^-1 # (right_inv f b')^-1 # q))
  (eq_of_rel Q q),
  from
  natural_square_tr (fun w : (Σz : B \* B => Q z.1 z.2), eq_of_rel Q w.2)
  (sigma_eq (prod_eq (right_inv f b) (right_inv f b')) H1),
  krewrite (ap_compose' (class_of Q)) at H2,
  krewrite (ap_compose' (fun z : B \* B => z.1)) at H2,
  rewrite sigma.ap_pr1 at H2, rewrite sigma_eq_pr1 at H2,
  krewrite prod.ap_pr1 at H2, krewrite prod_eq_pr1 at H2,
  krewrite (ap_compose' (class_of Q) (fun x : (Σz : B \* B => Q z.1 z.2), x.1.2)) at H2,
  krewrite (ap_compose' (fun z : B \* B => z.2)) at H2,
  rewrite sigma.ap_pr1 at H2, rewrite sigma_eq_pr1 at H2,
  krewrite prod.ap_pr2 at H2, krewrite prod_eq_pr2 at H2,
  apply H2 } },
  { intro qa, induction qa with a a a' r,
  { apply ap (class_of R), apply left_inv },
  { apply eq_pathover, rewrite [ap_id,(ap_compose' (quotient.elim _ _))],
  do 2 krewrite elim_eq_of_rel,
  have H1 : pathover (fun z : A \* A => R z.1 z.2)
  ((left_inv f a)^-1 # (left_inv f a')^-1 # r)
  (prod_eq (left_inv f a) (left_inv f a')) r,
Proof. apply pathover_of_eq_tr, krewrite [prod_eq_inv,prod_eq_transport] end,
  have H2 : square
  (ap (fun x : (Σz : A \* A => R z.1 z.2), class_of R x.1.1)
  (sigma_eq (prod_eq (left_inv f a) (left_inv f a')) H1))
  (ap (fun x : (Σz : A \* A => R z.1 z.2), class_of R x.1.2)
  (sigma_eq (prod_eq (left_inv f a) (left_inv f a')) H1))
  (eq_of_rel R ((left_inv f a)^-1 # (left_inv f a')^-1 # r))
  (eq_of_rel R r),
Proof.
  exact
  natural_square_tr (fun w : (Σz : A \* A => R z.1 z.2), eq_of_rel R w.2)
  (sigma_eq (prod_eq (left_inv f a) (left_inv f a')) H1)
Defined.,
  krewrite (ap_compose' (class_of R)) at H2,
  krewrite (ap_compose' (fun z : A \* A => z.1)) at H2,
  rewrite sigma.ap_pr1 at H2, rewrite sigma_eq_pr1 at H2,
  krewrite prod.ap_pr1 at H2, krewrite prod_eq_pr1 at H2,
  krewrite (ap_compose' (class_of R) (fun x : (Σz : A \* A => R z.1 z.2), x.1.2)) at H2,
  krewrite (ap_compose' (fun z : A \* A => z.2)) at H2,
  rewrite sigma.ap_pr1 at H2, rewrite sigma_eq_pr1 at H2,
  krewrite prod.ap_pr2 at H2, krewrite prod_eq_pr2 at H2,
  have H3 :
  (k (f^-1 (f a)) (f^-1 (f a')))^-1
  ((right_inv f (f a))^-1 # (right_inv f (f a'))^-1 # k a a' r)
  = (left_inv f a)^-1 # (left_inv f a')^-1 # r,
Proof.
  rewrite [adj f a,adj f a',ap_inv',ap_inv'],
  rewrite [-(tr_compose _ f (left_inv f a')^-1 (k a a' r)),
  -(tr_compose _ f (left_inv f a)^-1)],
  rewrite [-(fn_tr_eq_tr_fn (left_inv f a')^-1 (fun x => k a x) r),
  -(fn_tr_eq_tr_fn (left_inv f a)^-1
  (fun x => k x (f^-1 (f a')))),
  left_inv (k _ _)]
Defined.,
  rewrite H3, apply H2 } }
Defined.
Defined.

section
  variables {A : Type} (R : A -> A -> Type)
  {B : Type} (Q : B -> B -> Type)
  (f : A <~> B) (k : forall a a' : A, R a a' <~> Q (f a) (f a'))
  include f k

  (* This could also be proved using ua, but then it wouldn't compute *)
  protectedDefinition equiv : quotient R <~> quotient Q.
  equiv.mk (quotient.functor R Q f k) _
Defined.


Defined. quotient
