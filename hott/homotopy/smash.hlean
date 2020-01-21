(*
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

The Smash Product of Types.

OneDefinition is the cofiber of the map
    wedge A B -> A \* B
However, we define it (equivalently) as the pushout of the maps A + B -> 2 and A + B -> A \* B.
*)

import homotopy.circle homotopy.join types.pointed homotopy.cofiber homotopy.wedge

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge

namespace smash

  variables {A B : pType}

  section
  open pushout

Definition prod_of_sum (u : A + B) : A \* B.
  by induction u with a b; exact (a, (point _)); exact ((point _), b)

Definition bool_of_sum (u : A + B) : bool.
  by induction u; exact ff; exact tt

Definition smash' (A B : pType) : Type . pushout (@prod_of_sum A B) (@bool_of_sum A B)
  protectedDefinition mk' (a : A) (b : B) : smash' A B . inl (a, b)

Definition pointed_smash' [instance] (A B : pType) : pointed (smash' A B).
  pointed.mk (smash.mk' (point _) pt)
Definition smash (A B : pType) : pType.
  pointed.mk' (smash' A B)

  infixr ` ∧ ` . smash

  protectedDefinition mk (a : A) (b : B) : A ∧ B . inl (a, b)
Definition auxl : smash A B . inr ff
Definition auxr : smash A B . inr tt
Definition gluel (a : A) : smash.mk a (point _) = auxl :> smash A B . glue (inl a)
Definition gluer (b : B) : smash.mk (point _) b = auxr :> smash A B . glue (inr b)

Defined.

Definition gluel' (a a' : A) : smash.mk a (point _) = smash.mk a' (point _) :> smash A B.
  gluel a @ (gluel a')^-1
Definition gluer' (b b' : B) : smash.mk (point _) b = smash.mk (point _) b' :> smash A B.
  gluer b @ (gluer b')^-1
Definition glue (a : A) (b : B) : smash.mk a (point _) = smash.mk (point _) b.
  gluel' a (point _) @ gluer' (point _) b

Definition glue_pt_left (b : B) : glue (Point A) b = gluer' (point _) b.
  whisker_right _ (con_pV _) @ (concat_1p _)

Definition glue_pt_right (a : A) : glue a (Point B) = gluel' a (point _).
  proof whisker_left _ (con_pV _) qed

Definition ap_mk_left {a a' : A} (p : a = a') : ap (fun a => smash.mk a (Point B)) p = gluel' a a'.
  !ap_is_constant

Definition ap_mk_right {b b' : B} (p : b = b') : ap (smash.mk (Point A)) p = gluer' b b'.
  !ap_is_constant

  protectedDefinition rec {P : smash A B -> Type} (Pmk : forall a b, P (smash.mk a b))
    (Pl : P auxl) (Pr : P auxr) (Pgl : forall a, Pmk a (point _) =[gluel a] Pl)
    (Pgr : forall b, Pmk (point _) b =[gluer b] Pr) (x : smash' A B) : P x.
Proof.
    induction x with x b u,
    { induction x with a b, exact Pmk a b },
    { induction b, exact Pl, exact Pr },
    { induction u: esimp,
      { apply Pgl },
      { apply Pgr }}
Defined.

Definition rec_gluel {P : smash A B -> Type} {Pmk : forall a b, P (smash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : forall a, Pmk a (point _) =[gluel a] Pl)
    (Pgr : forall b, Pmk (point _) b =[gluer b] Pr) (a : A) :
    apd (smash.rec Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a.
  !pushout.rec_glue

Definition rec_gluer {P : smash A B -> Type} {Pmk : forall a b, P (smash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : forall a, Pmk a (point _) =[gluel a] Pl)
    (Pgr : forall b, Pmk (point _) b =[gluer b] Pr) (b : B) :
    apd (smash.rec Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b.
  !pushout.rec_glue

Definition rec_glue {P : smash A B -> Type} {Pmk : forall a b, P (smash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : forall a, Pmk a (point _) =[gluel a] Pl)
    (Pgr : forall b, Pmk (point _) b =[gluer b] Pr) (a : A) (b : B) :
    apd (smash.rec Pmk Pl Pr Pgl Pgr) (glue a b) =
      (Pgl a @o (Pgl (point _))^-1ᵒ) @o (Pgr (point _) @o (Pgr b)^-1ᵒ).
  by rewrite [↑glue, ↑gluel', ↑gluer', +apd_con, +apd_inv, +rec_gluel, +rec_gluer]

  protectedDefinition elim {P : Type} (Pmk : forall a b, P) (Pl Pr : P)
    (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B, Pmk (point _) b = Pr) (x : smash' A B) : P.
  smash.rec Pmk Pl Pr (fun a => pathover_of_eq _ (Pgl a)) (fun b => pathover_of_eq _ (Pgr b)) x

  (* an elim where you are forced to make (Pgl (point _)) and (Pgl (point _)) to be reflexivity *)
  protectedDefinition elim' {P : Type} (Pmk : forall a b, P)
    (Pgl : forall a : A, Pmk a (point _) = Pmk (point _) pt) (Pgr : forall b : B, Pmk (point _) b = Pmk (point _) pt)
    (ql : Pgl (point _) = idp) (qr : Pgr (point _) = idp) (x : smash' A B) : P.
  smash.elim Pmk (Pmk (point _) pt) (Pmk (point _) pt) Pgl Pgr x

Definition elim_gluel {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
    (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B, Pmk (point _) b = Pr) (a : A) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a.
Proof.
    apply eq_of_fn_eq_fn_inv !(pathover_constant (@gluel A B a)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑smash.elim,rec_gluel],
Defined.

Definition elim_gluer {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
    (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B, Pmk (point _) b = Pr) (b : B) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b.
Proof.
    apply eq_of_fn_eq_fn_inv !(pathover_constant (@gluer A B b)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑smash.elim,rec_gluer],
Defined.

Definition elim_glue {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
    (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B, Pmk (point _) b = Pr) (a : A) (b : B) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (glue a b) = (Pgl a @ (Pgl (point _))^-1) @ (Pgr (point _) @ (Pgr b)^-1).
  by rewrite [↑glue, ↑gluel', ↑gluer', +ap_con, +ap_inv, +elim_gluel, +elim_gluer]

Defined. smash
open smash



namespace smash

  variables {A B : pType}

Definition of_smash_pbool (x : smash A pbool) : A.
Proof.
    induction x,
    { induction b, exact (point _), exact a },
    { exact (point _) },
    { exact (point _) },
    { reflexivity },
    { induction b: reflexivity }
Defined.

Definition smash_pbool_pequiv (A : pType) : smash A pbool <~>* A.
Proof.
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact of_smash_pbool },
      { intro a, exact smash.mk a tt },
      { intro a, reflexivity },
      { exact abstract begin intro x, induction x,
        { induction b, exact gluer' tt (point _) @ gluel' (point _) a, reflexivity },
        { exact gluer' tt ff @ gluel (point _), },
        { exact gluer tt, },
        { apply eq_pathover_id_right,
          refine ap_compose (fun a => smash.mk a tt) _ _ @ ap02 _ !elim_gluel @ph _,
          apply square_of_eq_top, refine (concat_pp_p _ _ _)^-1 @ whisker_right _ (concat_1p _)^-1 },
        { apply eq_pathover_id_right,
          refine ap_compose (fun a => smash.mk a tt) _ _ @ ap02 _ !elim_gluer @ph _,
          induction b: esimp,
          { apply square_of_eq_top,
            refine whisker_left _ (con_pV _) @ (concat_p1 _) @ whisker_right _ (concat_1p _)^-1 },
          { apply square_of_eq idp }} end end }},
    { reflexivity }
Defined.

Defined. smash
