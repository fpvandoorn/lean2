(*
Copyright (c) 2015-16 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz, Jakob von Raumer

Declaration and properties of the pushout
*)

import .quotient types.sigma types.arrow_2

open quotient eq sum equiv is_trunc pointed

namespace pushout
section

parameters {TL BL TR : Type} (f : TL -> BL) (g : TL -> TR)

  local abbreviation A . BL + TR
  inductive pushout_rel : A -> A -> Type.
  | Rmk : forall (x : TL), pushout_rel (inl (f x)) (inr (g x))
  open pushout_rel
  local abbreviation R . pushout_rel

Definition pushout : Type . quotient R (* TODO: define this in root namespace *)

  parameters {f g}
Definition inl (x : BL) : pushout.
  class_of R (inl x)

Definition inr (x : TR) : pushout.
  class_of R (inr x)

Definition glue (x : TL) : inl (f x) = inr (g x).
  eq_of_rel pushout_rel (Rmk f g x)

  protectedDefinition rec {P : pushout -> Type} (Pinl : forall (x : BL), P (inl x))
  (Pinr : forall (x : TR), P (inr x)) (Pglue : forall (x : TL), Pinl (f x) =[glue x] Pinr (g x))
  (y : pushout) : P y.
Proof.
  induction y,
  { cases a,
  apply Pinl,
  apply Pinr},
  { cases H, apply Pglue}
Defined.

  protectedDefinition rec_on {P : pushout -> Type} (y : pushout)
  (Pinl : forall (x : BL), P (inl x)) (Pinr : forall (x : TR), P (inr x))
  (Pglue : forall (x : TL), Pinl (f x) =[glue x] Pinr (g x)) : P y.
  rec Pinl Pinr Pglue y

Definition rec_glue {P : pushout -> Type} (Pinl : forall (x : BL), P (inl x))
  (Pinr : forall (x : TR), P (inr x)) (Pglue : forall (x : TL), Pinl (f x) =[glue x] Pinr (g x))
  (x : TL) : apd (rec Pinl Pinr Pglue) (glue x) = Pglue x.
  !rec_eq_of_rel

  protectedDefinition elim {P : Type} (Pinl : BL -> P) (Pinr : TR -> P)
  (Pglue : forall (x : TL), Pinl (f x) = Pinr (g x)) (y : pushout) : P.
  rec Pinl Pinr (fun x => pathover_of_eq _ (Pglue x)) y

  protectedDefinition elim_on {P : Type} (y : pushout) (Pinl : BL -> P)
  (Pinr : TR -> P) (Pglue : forall (x : TL), Pinl (f x) = Pinr (g x)) : P.
  elim Pinl Pinr Pglue y

Definition elim_glue {P : Type} (Pinl : BL -> P) (Pinr : TR -> P)
  (Pglue : forall (x : TL), Pinl (f x) = Pinr (g x)) (x : TL)
  : ap (elim Pinl Pinr Pglue) (glue x) = Pglue x.
Proof.
  apply eq_of_fn_eq_fn_inv !(pathover_constant (glue x)),
  rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑pushout.elim,rec_glue],
Defined.

  protectedDefinition elim_type (Pinl : BL -> Type) (Pinr : TR -> Type)
  (Pglue : forall (x : TL), Pinl (f x) <~> Pinr (g x)) : pushout -> Type.
  quotient.elim_type (sum.rec Pinl Pinr)
Proof. intro v v' r, induction r, apply Pglue end

  protectedDefinition elim_type_on (y : pushout) (Pinl : BL -> Type)
  (Pinr : TR -> Type) (Pglue : forall (x : TL), Pinl (f x) <~> Pinr (g x)) : Type.
  elim_type Pinl Pinr Pglue y

Definition elim_type_glue (Pinl : BL -> Type) (Pinr : TR -> Type)
  (Pglue : forall (x : TL), Pinl (f x) <~> Pinr (g x)) (x : TL)
  : transport (elim_type Pinl Pinr Pglue) (glue x) = Pglue x.
  !elim_type_eq_of_rel_fn

Definition elim_type_glue_inv (Pinl : BL -> Type) (Pinr : TR -> Type)
  (Pglue : forall (x : TL), Pinl (f x) <~> Pinr (g x)) (x : TL)
  : transport (elim_type Pinl Pinr Pglue) (glue x)^-1 = to_inv (Pglue x).
  !elim_type_eq_of_rel_inv

  protectedDefinition rec_prop {P : pushout -> Type} [H : forall x, is_prop (P x)]
  (Pinl : forall (x : BL), P (inl x)) (Pinr : forall (x : TR), P (inr x)) (y : pushout).
  rec Pinl Pinr (fun x => !is_prop.elimo) y

  protectedDefinition elim_prop {P : Type} [H : is_prop P] (Pinl : BL -> P) (Pinr : TR -> P)
  (y : pushout) : P.
  elim Pinl Pinr (fun a => !is_prop.elim) y

Defined.
Defined. pushout







open sigma

namespace pushout

  variables {TL BL TR : Type} (f : TL -> BL) (g : TL -> TR)

  protectedDefinition elim_inl {P : Type} (Pinl : BL -> P) (Pinr : TR -> P)
  (Pglue : forall (x : TL), Pinl (f x) = Pinr (g x)) {b b' : BL} (p : b = b')
  : ap (pushout.elim Pinl Pinr Pglue) (ap inl p) = ap Pinl p.
  !ap_compose^-1

  protectedDefinition elim_inr {P : Type} (Pinl : BL -> P) (Pinr : TR -> P)
  (Pglue : forall (x : TL), Pinl (f x) = Pinr (g x)) {b b' : TR} (p : b = b')
  : ap (pushout.elim Pinl Pinr Pglue) (ap inr p) = ap Pinr p.
  !ap_compose^-1

  (* The non-dependent universal property *)
Definition pushout_arrow_equiv (C : Type)
  : (pushout f g -> C) <~> (Σ(i : BL -> C) (j : TR -> C), forall c, i (f c) = j (g c)).
Proof.
  fapply equiv.MK,
  { intro f, exact ⟨fun x => f (inl x), fun x => f (inr x), fun x => ap f (glue x)⟩},
  { intro v x, induction v with i w, induction w with j p, induction x,
  exact (i a), exact (j a), exact (p x)},
  { intro v, induction v with i w, induction w with j p, esimp,
  apply ap (fun p => ⟨i, j, p⟩), apply eq_of_homotopy, intro x, apply elim_glue},
  { intro f, apply eq_of_homotopy, intro x, induction x: esimp,
  apply eq_pathover, apply hdeg_square, esimp, apply elim_glue},
Defined.

  (* glue squares *)
  protectedDefinition glue_square {x x' : TL} (p : x = x')
  : square (glue x) (glue x') (ap inl (ap f p)) (ap inr (ap g p)).
  by cases p; apply vrefl

Defined. pushout

open function sigma.ops

namespace pushout

  (* The flattening lemma *)
  section

  universe variable u
  parameters {TL BL TR : Type} (f : TL -> BL) (g : TL -> TR)
  (Pinl : BL -> Type.{u}) (Pinr : TR -> Type.{u})
  (Pglue : forall (x : TL), Pinl (f x) <~> Pinr (g x))
  include Pglue

  local abbreviation A . BL + TR
  local abbreviation R : A -> A -> Type . pushout_rel f g
  local abbreviation P . pushout.elim_type Pinl Pinr Pglue

  local abbreviation F : sigma (Pinl o f) -> sigma Pinl.
  fun z => ⟨ f z.1 , z.2 ⟩

  local abbreviation G : sigma (Pinl o f) -> sigma Pinr.
  fun z => ⟨ g z.1 , Pglue z.1 z.2 ⟩

  protectedDefinition flattening : sigma P <~> pushout F G.
Proof.
  apply equiv.trans !quotient.flattening.flattening_lemma,
  fapply equiv.MK,
  { intro q, induction q with z z z' fr,
  { induction z with a p, induction a with x x,
  { exact inl ⟨x, p⟩ },
  { exact inr ⟨x, p⟩ } },
  { induction fr with a a' r p, induction r with x,
  exact glue ⟨x, p⟩ } },
  { intro q, induction q with xp xp xp,
  { exact class_of _ ⟨sum.inl xp.1, xp.2⟩ },
  { exact class_of _ ⟨sum.inr xp.1, xp.2⟩ },
  { apply eq_of_rel, constructor } },
  { intro q, induction q with xp xp xp: induction xp with x p,
  { apply ap inl, reflexivity },
  { apply ap inr, reflexivity },
  { unfold F, unfold G, apply eq_pathover,
  rewrite [ap_id,ap_compose' (quotient.elim _ _)],
  krewrite elim_glue, krewrite elim_eq_of_rel, apply hrefl } },
  { intro q, induction q with z z z' fr,
  { induction z with a p, induction a with x x,
  { reflexivity },
  { reflexivity } },
  { induction fr with a a' r p, induction r with x,
  esimp, apply eq_pathover,
  rewrite [ap_id,ap_compose' (pushout.elim _ _ _)],
  krewrite elim_eq_of_rel, krewrite elim_glue, apply hrefl } }
Defined.
Defined.

  (* Commutativity of pushouts *)
  section
  variables {TL BL TR : Type} (f : TL -> BL) (g : TL -> TR)

  protectedDefinition transpose : pushout f g -> pushout g f.
Proof.
  intro x, induction x, apply inr a, apply inl a, apply !glue^-1
Defined.

  --TODO prove without krewrite?
  protectedDefinition transpose_involutive (x : pushout f g) :
  pushout.transpose g f (pushout.transpose f g x) = x.
Proof.
  induction x, apply idp, apply idp,
  apply eq_pathover, refine _ @hp !ap_id^-1,
  refine !(ap_compose (pushout.transpose _ _)) @ph _, esimp[pushout.transpose],
  krewrite [elim_glue, ap_inv, elim_glue, inv_inv], apply hrfl
Defined.

  protectedDefinition symm : pushout f g <~> pushout g f.
Proof.
  fapply equiv.MK, do 2 exact !pushout.transpose,
  do 2 (intro x; apply pushout.transpose_involutive),
Defined.

Defined.

  (* Functoriality of pushouts *)
  section
  section lemmas
  variables {X : Type} {x₀ x₁ x₂ x₃ : X}
  (p : x₀ = x₁) (q : x₁ = x₂) (r : x₂ = x₃)
  privateDefinition is_equiv_functor_lemma₁
  : (r @ ((p @ q @ r)^-1 @ p)) = q^-1.
  by cases p; cases r; cases q; reflexivity

  privateDefinition is_equiv_functor_lemma₂
  : (p @ q @ r)^-1 @ (p @ q) = r^-1.
  by cases p; cases r; cases q; reflexivity
Defined. lemmas

  variables {TL BL TR : Type} {f : TL -> BL} {g : TL -> TR}
  {TL' BL' TR' : Type} {f' : TL' -> BL'} {g' : TL' -> TR'}
  (tl : TL -> TL') (bl : BL -> BL') (tr : TR -> TR')
  (fh : bl o f == f' o tl) (gh : tr o g == g' o tl)
  include fh gh

  protectedDefinition functor [unfold 16] : pushout f g -> pushout f' g'.
Proof.
  intro x, induction x with a b z,
  { exact inl (bl a) },
  { exact inr (tr b) },
  { exact (ap inl (fh z)) @ glue (tl z) @ (ap inr (gh z)^-1) }
Defined.

  protectedDefinition ap_functor_inl [unfold 18] {x x' : BL} (p : x = x')
  : ap (pushout.functor tl bl tr fh gh) (ap inl p) = ap inl (ap bl p).
  by cases p; reflexivity

  protectedDefinition ap_functor_inr [unfold 18] {x x' : TR} (p : x = x')
  : ap (pushout.functor tl bl tr fh gh) (ap inr p) = ap inr (ap tr p).
  by cases p; reflexivity

  variables [ietl : is_equiv tl] [iebl : is_equiv bl] [ietr : is_equiv tr]
  include ietl iebl ietr

  open equiv is_equiv arrow
  protectedDefinition is_equiv_functor [instance]
  : is_equiv (pushout.functor tl bl tr fh gh).
  adjointify
  (pushout.functor tl bl tr fh gh)
  (pushout.functor tl^-1 bl^-1 tr^-1
  (inv_commute_of_commute tl bl f f' fh)
  (inv_commute_of_commute tl tr g g' gh))
  abstract begin
  intro x', induction x' with a' b' z',
  { apply ap inl, apply right_inv },
  { apply ap inr, apply right_inv },
  { apply eq_pathover,
  rewrite [ap_id,ap_compose' (pushout.functor tl bl tr fh gh)] =>
  krewrite elim_glue,
  rewrite [ap_inv,ap_con,ap_inv],
  krewrite [pushout.ap_functor_inr] => rewrite ap_con,
  krewrite [pushout.ap_functor_inl =>elim_glue],
  apply transpose,
  apply move_top_of_right, apply move_top_of_left',
  krewrite [-(ap_inv inl),-ap_con,-(ap_inv inr),-ap_con],
  apply move_top_of_right, apply move_top_of_left',
  krewrite [-ap_con,-(ap_inv inl),-ap_con],
  rewrite ap_bot_inv_commute_of_commute,
  apply eq_hconcat (ap02 inl
  (is_equiv_functor_lemma₁
  (right_inv bl (f' z'))
  (ap f' (right_inv tl z')^-1)
  (fh (tl^-1 z'))^-1)),
  rewrite [ap_inv f',inv_inv],
  rewrite ap_bot_inv_commute_of_commute,
  refine hconcat_eq _ (ap02 inr
  (is_equiv_functor_lemma₁
  (right_inv tr (g' z'))
  (ap g' (right_inv tl z')^-1)
  (gh (tl^-1 z'))^-1))^-1,
  rewrite [ap_inv g',inv_inv],
  apply pushout.glue_square }
Defined. end
  abstract begin
  intro x, induction x with a b z,
  { apply ap inl, apply left_inv },
  { apply ap inr, apply left_inv },
  { apply eq_pathover,
  rewrite [ap_id,ap_compose'
  (pushout.functor tl^-1 bl^-1 tr^-1 _ _)
  (pushout.functor tl bl tr _ _)] =>
  krewrite elim_glue,
  rewrite [ap_inv,ap_con,ap_inv],
  krewrite [pushout.ap_functor_inr] => rewrite ap_con,
  krewrite [pushout.ap_functor_inl =>elim_glue],
  apply transpose,
  apply move_top_of_right, apply move_top_of_left',
  krewrite [-(ap_inv inl),-ap_con,-(ap_inv inr),-ap_con],
  apply move_top_of_right, apply move_top_of_left',
  krewrite [-ap_con,-(ap_inv inl),-ap_con],
  rewrite inv_commute_of_commute_top,
  apply eq_hconcat (ap02 inl
  (is_equiv_functor_lemma₂
  (ap bl^-1 (fh z))^-1
  (left_inv bl (f z))
  (ap f (left_inv tl z)^-1))),
  rewrite [ap_inv f,inv_inv],
  rewrite inv_commute_of_commute_top,
  refine hconcat_eq _ (ap02 inr
  (is_equiv_functor_lemma₂
  (ap tr^-1 (gh z))^-1
  (left_inv tr (g z))
  (ap g (left_inv tl z)^-1)))^-1,
  rewrite [ap_inv g,inv_inv],
  apply pushout.glue_square }
Defined. end

Defined.

  (* version giving the equivalence *)
  section
  variables {TL BL TR : Type} (f : TL -> BL) (g : TL -> TR)
  {TL' BL' TR' : Type} (f' : TL' -> BL') (g' : TL' -> TR')
  (tl : TL <~> TL') (bl : BL <~> BL') (tr : TR <~> TR')
  (fh : bl o f == f' o tl) (gh : tr o g == g' o tl)
  include fh gh

  protectedDefinition equiv : pushout f g <~> pushout f' g'.
  equiv.mk (pushout.functor tl bl tr fh gh) _
Defined.

Definition pointed_pushout [instance] {TL BL TR : Type} [HTL : pointed TL]
  [HBL : pointed BL] [HTR : pointed TR] (f : TL -> BL) (g : TL -> TR) : pointed (pushout f g).
  pointed.mk (inl (point _))
Defined. pushout open pushout

Definition ppushout {TL BL TR : pType} (f : TL ->* BL) (g : TL ->* TR) : pType.
pointed.mk' (pushout f g)

namespace pushout
  section
  parameters {TL BL TR : pType} (f : TL ->* BL) (g : TL ->* TR)

  parameters {f g}
Definition pinl : BL ->* ppushout f g.
  Build_pMap inl idp

Definition pinr : TR ->* ppushout f g.
  Build_pMap inr ((ap inr (point_eq g))^-1 @ !glue^-1 @ (ap inl (point_eq f)))

Definition pglue (x : TL) : pinl (f x) = pinr (g x) . (* TODO do we need this? *)
  !glue

Defined.

  section
  variables {TL BL TR : pType} (f : TL ->* BL) (g : TL ->* TR)

  protectedDefinition psymm : ppushout f g <~>* ppushout g f.
Proof.
  fapply pequiv_of_equiv,
  { apply pushout.symm },
  { exact ap inr (point_eq f)^-1 @ !glue^-1 @ ap inl (point_eq g) }
Defined.

Defined.
Defined. pushout
