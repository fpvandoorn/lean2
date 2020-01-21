(*
Copyright (c) 2017 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egbert Rijke

*)

(*
The goal of this file is to extend the library of pointed types and pointed maps to support the library of prespectra

*)

import types.pointed2 .pointed_pi

open eq pointed

Definition psquare_of_phtpy_top {A B C D : pType}  {ftop : A ->* B} {fbot : C ->* D} {fleft : A ->* C} {fright : B ->* D} {ftop' : A ->* B} (phtpy : ftop ==* ftop') (psq : psquare ftop' fbot fleft fright) : psquare ftop fbot fleft fright.
Proof.
  induction phtpy using phomotopy_rec_idp, exact psq,
Defined.

Definition psquare_of_phtpy_bot {A B C D : pType} {ftop : A ->* B} {fbot : C ->* D} {fleft : A ->* C} {fright : B ->* D} {fbot' : C ->* D} (phtpy : fbot ==* fbot') (psq : psquare ftop fbot' fleft fright) : psquare ftop fbot fleft fright.
Proof.
  induction phtpy using phomotopy_rec_idp, exact psq,
Defined.

Definition psquare_of_phtpy_left {A B C D : pType} {ftop : A ->* B} {fbot : C ->* D} {fleft : A ->* C} {fright : B ->* D} {fleft' : A ->* C} (phtpy : fleft ==* fleft') (psq : psquare ftop fbot fleft fright) : psquare ftop fbot fleft' fright.
Proof.
  induction phtpy using phomotopy_rec_idp, exact psq,
Defined.

Definition psquare_of_phtpy_right {A B C D : pType} {ftop : A ->* B} {fbot : C ->* D} {fleft : A ->* C} {fright : B ->* D} {fright' : B ->* D} (phtpy : fright ==* fright') (psq : psquare ftop fbot fleft fright) : psquare ftop fbot fleft fright'.
Proof.
  induction phtpy using phomotopy_rec_idp, exact psq,
Defined.

Definition psquare_of_pid_top_bot {A B : pType} {fleft : A ->* B} {fright : A ->* B} (phtpy : fright ==* fleft) : psquare (pid A) (pid B) fleft fright.
psquare_of_phomotopy ((pcompose_pid fright) @* phtpy @* (pid_pcompose fleft)^-1*)

--print psquare_of_pid_top_bot

--fun phtpy => psquare_of_phomotopy ((pid_pcompose fleft) @* phtpy @* ((pcompose_pid fright)^-1*))

Definition psquare_of_pid_left_right {A B : pType} {ftop : A ->* B} {fbot : A ->* B} (phtpy : ftop ==* fbot) : psquare ftop fbot (pid A) (pid B).
psquare_of_phomotopy ((pid_pcompose ftop) @* phtpy @* ((pcompose_pid fbot)^-1*))

--print psquare_of_pid_left_right

Definition psquare_hcompose {A B C D E F : pType} {ftop : A ->* B} {fbot : D ->* E} {fleft : A ->* D} {fright : B ->* E} {gtop : B ->* C} {gbot : E ->* F} {gright : C ->* F} (psq_left : psquare ftop fbot fleft fright) (psq_right : psquare gtop gbot fright gright) : psquare (gtop o* ftop) (gbot o* fbot) fleft gright.
Proof.
  fapply psquare_of_phomotopy,
  refine (passoc gright gtop ftop)^-1* @* _ @* (passoc gbot fbot fleft)^-1*,
  refine (pwhisker_right ftop psq_right) @* (passoc gbot fright ftop) @* _,
  exact (pwhisker_left gbot psq_left),
Defined.

Definition psquare_vcompose {A B C D E F : pType} {ftop : A ->* B} {fbot : C ->* D} {fleft : A ->* C} {fright : B ->* D} {gbot : E ->* F} {gleft : C ->* E} {gright : D ->* F} (psq_top : psquare ftop fbot fleft fright) (psq_bot : psquare fbot gbot gleft gright) : psquare ftop gbot (gleft o* fleft) (gright o* fright).
Proof.
  fapply psquare_of_phomotopy,
  refine (passoc gright fright ftop) @* _ @* (passoc gbot gleft fleft),
  refine (pwhisker_left gright psq_top) @* _,
  refine (passoc gright fbot fleft)^-1* @* _,
  exact pwhisker_right fleft psq_bot,
Defined.

Definition psquare_of_pconst_top_bot {A B C D : pType} (fleft : A ->* C) (fright : B ->* D) : psquare (pconst A B) (pconst C D) fleft fright.
Proof.
  fapply psquare_of_phomotopy,
  refine (pcompose_pconst fright) @* _,
  exact (pconst_pcompose fleft)^-1*,
Defined.

Definition psquare_of_pconst_left_right {A B C D : pType} (ftop : A ->* B) (fbot : C ->* D) : psquare ftop fbot (pconst A C) (pconst B D).
Proof.
  fapply psquare_of_phomotopy,
  refine (pconst_pcompose ftop) @* _,
  exact (pcompose_pconst fbot)^-1*
Defined.

Definition psquare_of_pconst_top_left {A B C D : pType} (fbot : C ->* D) (fright : B ->* D) : psquare (pconst A B) fbot (pconst A C) fright.
Proof.
  fapply psquare_of_phomotopy,
  refine (pcompose_pconst fright) @* _,
  exact (pcompose_pconst fbot)^-1*,
Defined.

Definition psquare_of_pconst_bot_right {A B C D : pType} (ftop : A ->* B) (fleft : A ->* C) : psquare ftop (pconst C D) fleft (pconst B D).
Proof.
  fapply psquare_of_phomotopy,
  refine (pconst_pcompose ftop) @* _,
  exact (pconst_pcompose fleft)^-1*,
Defined.

Definition phsquare_of_phomotopy {A B : pType} {f g h i : A ->* B} {phtpy_top : f ==* g}
  {phtpy_bot : h ==* i} {phtpy_left : f ==* h} {phtpy_right : g ==* i}
  (H : phtpy_top @* phtpy_right ==* phtpy_left @* phtpy_bot) :
  phsquare phtpy_top phtpy_bot phtpy_left phtpy_right.
path_pforall H

Definition ptube_v {A B C D : pType} {ftop ftop' : A ->* B} (phtpy_top : ftop ==* ftop')
  {fbot fbot' : C ->* D} (phtpy_bot : fbot ==* fbot') {fleft : A ->* C} {fright : B ->* D}
  (psq_back : psquare ftop fbot fleft fright) (psq_front : psquare ftop' fbot' fleft fright) :
  Type.
phsquare (pwhisker_left fright phtpy_top) (pwhisker_right fleft phtpy_bot) psq_back psq_front

Definition ptube_h {A B C D : pType} {ftop : A ->* B} {fbot : C ->* D} {fleft fleft' : A ->* C}
  (phtpy_left : fleft ==* fleft') {fright fright' : B ->* D} (phtpy_right : fright ==* fright')
  (psq_back : psquare ftop fbot fleft fright) (psq_front : psquare ftop fbot fleft' fright') :
  Type.
phsquare (pwhisker_right ftop phtpy_right) (pwhisker_left fbot phtpy_left) psq_back psq_front

--print pinv_right_phomotopy_of_phomotopy

Definition psquare_inv_top_bot {A B C D : pType} {ftop : A <~>* B} {fbot : C <~>* D} {fleft : A ->* C} {fright : B ->* D} (psq : psquare ftop fbot fleft fright) : psquare ftop^-1ᵉ* fbot^-1ᵉ* fright fleft.
Proof.
  fapply psquare_of_phomotopy,
  refine (pinv_right_phomotopy_of_phomotopy _),
  refine _ @* (passoc fbot^-1ᵉ* fright ftop)^-1*,
  refine (pinv_left_phomotopy_of_phomotopy _)^-1*,
  exact psq,
Defined.

Definition p2homotopy_ty_point_eq {A B : pType} {f g : A ->* B} {H K : f ==* g} (htpy : H == K) : Type.
Proof.
  induction H with H p, exact p
Defined.  = whisker_right (point_eq g) (htpy (point _)) @
Proof.
induction K with K q, exact q
Defined.

--print p2homotopy_ty_point_eq

structure p2homotopy {A B : pType} {f g : A ->* B} (H K : f ==* g) : Type.
( to_2htpy : H == K)
( point_eq  : p2homotopy_ty_point_eq to_2htpy)

Definition ptube_v_phtpy_bot {A B C D : pType}
  {ftop ftop' : A ->* B} {phtpy_top : ftop ==* ftop'}
  {fbot fbot' : C ->* D} {phtpy_bot phtpy_bot' : fbot ==* fbot'} (ppi_htpy_bot : phtpy_bot ==* phtpy_bot')
  {fleft : A ->* C} {fright : B ->* D}
  {psq_back : psquare ftop fbot fleft fright}
  {psq_front : psquare ftop' fbot' fleft fright}
  (ptb : ptube_v phtpy_top phtpy_bot psq_back psq_front)
  : ptube_v phtpy_top phtpy_bot' psq_back psq_front
 .
Proof.
  induction ppi_htpy_bot using phomotopy_rec_idp,
  exact ptb,
Defined.

Definition ptube_v_eq_bot {A B C D : pType} {ftop ftop' : A ->* B} (htpy_top : ftop ==* ftop') {fbot fbot' : C ->* D} {htpy_bot htpy_bot' : fbot ==* fbot'} (p : htpy_bot = htpy_bot') {fleft : A ->* C} {fright : B ->* D} (psq_back : psquare ftop fbot fleft fright) (psq_front : psquare ftop' fbot' fleft fright) :
  ptube_v htpy_top htpy_bot psq_back psq_front -> ptube_v htpy_top htpy_bot' psq_back psq_front.
Proof.
  induction p,
  exact id,
Defined.

Definition ptube_v_left_inv {A B C D : pType} {ftop : A <~>* B} {fbot : C <~>* D} {fleft : A ->* C} {fright : B ->* D}
  (psq : psquare ftop fbot fleft fright) :
  ptube_v
  (pleft_inv ftop)
  (pleft_inv fbot)
  (psquare_hcompose psq (psquare_inv_top_bot psq))
  (psquare_of_pid_top_bot (reflexivity _)).
Proof.
  refine ptube_v_phtpy_bot _ _,
  exact pleft_inv fbot,
  exact (reflexivity _),
  fapply phsquare_of_phomotopy, repeat exact sorry,
Defined.
