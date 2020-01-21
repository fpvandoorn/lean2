(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the reduced suspension
red_susp X
*)

import hit.two_quotient types.pointed algebra.e_closure

open simple_two_quotient eq unit pointed e_closure susp function

namespace red_susp
section

  parameter {A : pType}

  inductive red_susp_R : unit -> unit -> Type.
  | Rmk : forall (a : A), red_susp_R star star
  open red_susp_R
  inductive red_susp_Q : forall (x : unit), e_closure red_susp_R x x -> Type.
  | Qmk : red_susp_Q [Rmk (point _)]
  open red_susp_Q
  local abbreviation R . red_susp_R
  local abbreviation Q . red_susp_Q

  parameter (A)
Definition red_susp' : Type . simple_two_quotient R Q
  parameter {A}
Definition base' : red_susp'.
  incl0 R Q star
  parameter (A)
Definition red_susp : pType . pointed.MK red_susp' base'
  parameter {A}

Definition base : red_susp.
  base'

Definition equator (a : A) : base = base.
  incl1 R Q (Rmk a)

Definition equator_pt : equator (point _) = idp.
  incl2 R Q Qmk

  protectedDefinition rec {P : red_susp -> Type} (Pb : P base) (Pm : forall (a : A), Pb =[equator a] Pb)
    (Pe : change_path equator_pt (Pm (point _)) = idpo) (x : red_susp') : P x.
Proof.
    induction x,
    { induction a, exact Pb},
    { induction s, exact Pm a},
    { induction q, esimp, exact Pe}
Defined.

  protectedDefinition rec_on {P : red_susp -> Type} (x : red_susp') (Pb : P base)
    (Pm : forall (a : A), Pb =[equator a] Pb) (Pe : change_path equator_pt (Pm (point _)) = idpo) : P x.
  red_susp.rec Pb Pm Pe x

Definition rec_equator {P : red_susp -> Type} (Pb : P base) (Pm : forall (a : A), Pb =[equator a] Pb)
    (Pe : change_path equator_pt (Pm (point _)) = idpo) (a : A)
    : apd (rec Pb Pm Pe) (equator a) = Pm a.
  !rec_incl1

  protectedDefinition elim {P : Type} (Pb : P) (Pm : forall (a : A), Pb = Pb)
    (Pe : Pm (point _) = idp) (x : red_susp') : P.
Proof.
    induction x,
      exact Pb,
      induction s, exact Pm a,
      induction q, exact Pe
Defined.

 protectedDefinition elim_on {P : Type} (x : red_susp') (Pb : P)
    (Pm : forall (a : A), Pb = Pb) (Pe : Pm (point _) = idp) : P.
  elim Pb Pm Pe x

Definition elim_equator {P : Type} {Pb : P} {Pm : forall (a : A), Pb = Pb}
    (Pe : Pm (point _) = idp) (a : A)
    : ap (elim Pb Pm Pe) (equator a) = Pm a.
  !elim_incl1

Definition elim_equator_pt {P : Type} (Pb : P) (Pm : forall (a : A), Pb = Pb)
    (Pe : Pm (point _) = idp) : square (ap02 (elim Pb Pm Pe) equator_pt) Pe (elim_equator Pe (point _)) idp.
  !elim_incl2

Defined.
Defined. red_susp



--attribute red_susp.elim_type [unfold 9]

--attribute red_susp.elim_type_on [unfold 6]

namespace red_susp

  protectedDefinition pelim' {A P : pType} (f : A ->* loops P) : red_susp' A -> P.
  red_susp.elim (point _) f (point_eq f)

  protectedDefinition pelim {A P : pType} (f : A ->* loops P) : red_susp A ->* P.
  Build_pMap (red_susp.pelim' f) idp

Definition susp_of_red_susp {A : pType} (x : red_susp A) : susp A.
Proof.
    induction x,
    { exact !north },
    { exact merid a @ (merid (point _))^-1 },
    { apply con.right_inv }
Defined.

Definition red_susp_of_susp {A : pType} (x : susp A) : red_susp A.
Proof.
    induction x,
    { exact (point _) },
    { exact (point _) },
    { exact equator a }
Defined.

Definition red_susp_helper_lemma {A : Type} {a : A} {p₁ p₂ : a = a} (q : p₁ = p₂) (q' : p₂ = idp)
    : square (q ◾ (q @ q')⁻²) idp (con.right_inv p₁) q'.
Proof. induction q, cases q', exact hrfl end

Definition red_susp_equiv_susp (A : pType) : red_susp A <~> susp A.
Proof.
    fapply equiv.MK,
    { exact susp_of_red_susp },
    { exact red_susp_of_susp },
    { exact abstract begin intro x, induction x,
      { reflexivity },
      { exact merid (point _) },
      { apply eq_pathover_id_right,
        refine ap_compose susp_of_red_susp _ _ @ ap02 _ !elim_merid @ !elim_equator @ph _,
        apply whisker_bl, exact hrfl } end end },
    { exact abstract begin intro x, induction x,
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        refine ap_compose red_susp_of_susp _ _ @ (ap02 _ !elim_equator @ _) @ !ap_id^-1,
        exact (ap_pp _ _ _) @ whisker_left _ !ap_inv @ !elim_merid ◾ (!elim_merid @ equator_pt)⁻² },
      { refine !change_path_eq_pathover @ ap eq_pathover !eq_hconcat_eq_hdeg_square @ _,
        refine @(ap (eq_pathover o hdeg_square)) _ idp _, symmetry, apply eq_bot_of_square,
        refine _ @h !ap02_id^-1ʰ, refine !ap02_compose @h _,
        apply move_top_of_left', refine whisker_right _ !ap_inv^-1 @ (ap_pp _ _ _)^-1 @ph _,
        refine ap02 _ (eq_bot_of_square !elim_equator_pt)^-1 @ph _,
        refine transpose (ap_pp _ _ _)_right_inv_sq @h _, apply red_susp_helper_lemma } end end }
Defined.

  (* a second proof that the reduced suspension is the suspension, by first proving
     a new induction principle for the reduced suspension *)

  protectedDefinition susp_rec {A : pType} {P : red_susp A -> Type} (P0 : P base)
    (P1 : forall a, P0 =[equator a] P0) (x : red_susp' A) : P x.
Proof.
    induction x,
    { exact P0 },
    { refine change_path _ (P1 a @o (P1 (point _))^-1ᵒ), exact whisker_left (equator a) equator_pt⁻² },
    { refine !change_path_con^-1 @ _, refine ap (fun x => change_path x _) _ @ cono_invo_eq_idpo idp,
      exact whisker_left_inverse2 equator_pt }
Defined.

Definition red_susp_equiv_susp' (A : pType) : red_susp A <~> susp A.
Proof.
    fapply equiv.MK,
    { exact susp_of_red_susp },
    { exact red_susp_of_susp },
    { exact abstract begin intro x, induction x,
      { reflexivity },
      { exact merid (point _) },
      { apply eq_pathover_id_right,
        refine ap_compose susp_of_red_susp _ _ @ ap02 _ !elim_merid @ !elim_equator @ph _,
        apply whisker_bl, exact hrfl } end end },
    { intro x, induction x using red_susp.susp_rec,
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        refine ap_compose red_susp_of_susp _ _ @ (ap02 _ !elim_equator @ _) @ !ap_id^-1,
        exact (ap_pp _ _ _) @ whisker_left _ !ap_inv @ !elim_merid ◾ (!elim_merid @ equator_pt)⁻² }}
Defined.


Defined. red_susp
