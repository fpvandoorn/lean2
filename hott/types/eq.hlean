(*
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Partially ported from Coq HoTT
Theorems about path types (identity types)
*)

import types.sigma
open eq sigma sigma.ops equiv is_equiv is_trunc

namespace eq
  (* Path spaces *)
  section
  variables {A B : Type} {a a₁ a₂ a₃ a₄ a' : A} {b b1 b2 : B} {f g : A -> B} {h : B -> A}
            {p p' p'' : a₁ = a₂}

  (* The path spaces of a path space are not, of course, determined; they are just the
      higher-dimensional structure of the original space. *)

  (* some lemmas about whiskering or other higher paths *)

Definition whisker_left_con_right (p : a₁ = a₂) {q q' q'' : a₂ = a₃} (r : q = q') (s : q' = q'')
    : whisker_left p (r @ s) = whisker_left p r @ whisker_left p s.
Proof.
    induction p, induction r, induction s, reflexivity
Defined.

Definition whisker_right_con_right (q : a₂ = a₃) (r : p = p') (s : p' = p'')
    : whisker_right q (r @ s) = whisker_right q r @ whisker_right q s.
Proof.
    induction q, induction r, induction s, reflexivity
Defined.

Definition whisker_left_con_left (p : a₁ = a₂) (p' : a₂ = a₃) {q q' : a₃ = a₄} (r : q = q')
    : whisker_left (p @ p') r = (concat_pp_p _ _ _) @ whisker_left p (whisker_left p' r) @ (concat_pp_p _ _ _)'.
Proof.
    induction p', induction p, induction r, induction q, reflexivity
Defined.

Definition whisker_right_con_left {p p' : a₁ = a₂} (q : a₂ = a₃) (q' : a₃ = a₄) (r : p = p')
    : whisker_right (q @ q') r = (concat_pp_p _ _ _)' @ whisker_right q' (whisker_right q r) @ (concat_pp_p _ _ _).
Proof.
    induction q', induction q, induction r, induction p, reflexivity
Defined.

Definition whisker_left_inv_left (p : a₂ = a₁) {q q' : a₂ = a₃} (r : q = q')
    : !con_inv_cancel_left^-1 @ whisker_left p (whisker_left p^-1 r) @ !con_inv_cancel_left = r.
Proof.
    induction p, induction r, induction q, reflexivity
Defined.

Definition whisker_left_inv (p : a₁ = a₂) {q q' : a₂ = a₃} (r : q = q')
    : whisker_left p r^-1 = (whisker_left p r)^-1.
  by induction r; reflexivity

Definition whisker_right_inv {p p' : a₁ = a₂} (q : a₂ = a₃) (r : p = p')
    : whisker_right q r^-1 = (whisker_right q r)^-1.
  by induction r; reflexivity

Definition ap_eq_apd10 {B : A -> Type} {f g : forall a, B a} (p : f = g) (a : A) :
    ap (fun h => h a) p = apd10 p a.
  by induction p; reflexivity

Definition inverse2_right_inv (r : p = p') : r ◾ inverse2 r @ con.right_inv p' = con.right_inv p.
  by induction r;induction p;reflexivity

Definition inverse2_left_inv (r : p = p') : inverse2 r ◾ r @ con.left_inv p' = con.left_inv p.
  by induction r;induction p;reflexivity

Definition ap_con_right_inv (f : A -> B) (p : a₁ = a₂)
    : ap_con f p p^-1 @ whisker_left _ (ap_inv f p) @ con.right_inv (ap f p)
      = ap (ap f) (con.right_inv p).
  by induction p;reflexivity

Definition ap_con_left_inv (f : A -> B) (p : a₁ = a₂)
    : ap_con f p^-1 p @ whisker_right _ (ap_inv f p) @ con.left_inv (ap f p)
      = ap (ap f) (con.left_inv p).
  by induction p;reflexivity

Definition idp_con_whisker_left {q q' : a₂ = a₃} (r : q = q') :
  (concat_1p _)^-1 @ whisker_left idp r = r @ (concat_1p _)^-1.
  by induction r;induction q;reflexivity

Definition whisker_left_idp_con {q q' : a₂ = a₃} (r : q = q') :
  whisker_left idp r @ (concat_1p _) = (concat_1p _) @ r.
  by induction r;induction q;reflexivity

Definition idp_con_idp {p : a = a} (q : p = idp) : idp_con p @ q = ap (fun p => idp @ p) q.
  by cases q;reflexivity

Definition ap_is_constant {A B : Type} {f : A -> B} {b : B} (p : forall x, f x = b)
    {x y : A} (q : x = y) : ap f q = p x @ (p y)^-1.
  by induction q;exact (con_pV _)^-1

Definition inv2_inv {p q : a = a'} (r : p = q) : inverse2 r^-1 = (inverse2 r)^-1.
  by induction r;reflexivity

Definition inv2_con {p p' p'' : a = a'} (r : p = p') (r' : p' = p'')
    : inverse2 (r @ r') = inverse2 r @ inverse2 r'.
  by induction r';induction r;reflexivity

Definition con2_inv {p₁ q₁ : a₁ = a₂} {p₂ q₂ : a₂ = a₃} (r₁ : p₁ = q₁) (r₂ : p₂ = q₂)
    : (r₁ ◾ r₂)^-1 = r₁^-1 ◾ r₂^-1.
  by induction r₁;induction r₂;reflexivity

Definition eq_con_inv_of_con_eq_whisker_left {A : Type} {a a₂ a₃ : A}
    {p : a = a₂} {q q' : a₂ = a₃} {r : a = a₃} (s' : q = q') (s : p @ q' = r) :
    eq_con_inv_of_con_eq (whisker_left p s' @ s)
      = eq_con_inv_of_con_eq s @ whisker_left r (inverse2 s')^-1.
  by induction s';induction q;induction s;reflexivity

Definition right_inv_eq_idp {A : Type} {a : A} {p : a = a} (r : p = idpath a) :
    con.right_inv p = r ◾ inverse2 r.
  by cases r;reflexivity

  (* Transporting in path spaces.

     There are potentially a lot of these lemmas, so we adopt a uniform naming scheme:

     - `l` means the left endpoint varies
     - `r` means the right endpoint varies
     - `F` means application of a function to that (varying) endpoint.
  *)

Definition eq_transport_l (p : a₁ = a₂) (q : a₁ = a₃)
    : transport (fun x => x = a₃) p q = p^-1 @ q.
  by induction p; exact (concat_1p _)^-1

Definition eq_transport_r (p : a₂ = a₃) (q : a₁ = a₂)
    : transport (fun x => a₁ = x) p q = q @ p.
  by induction p; reflexivity

Definition eq_transport_lr (p : a₁ = a₂) (q : a₁ = a₁)
    : transport (fun x => x = x) p q = p^-1 @ q @ p.
  by induction p; exact (concat_1p _)^-1

Definition eq_transport_Fl (p : a₁ = a₂) (q : f a₁ = b)
    : transport (fun x => f x = b) p q = (ap f p)^-1 @ q.
  by induction p; exact (concat_1p _)^-1

Definition eq_transport_Fr (p : a₁ = a₂) (q : b = f a₁)
    : transport (fun x => b = f x) p q = q @ (ap f p).
  by induction p; reflexivity

Definition eq_transport_FlFr (p : a₁ = a₂) (q : f a₁ = g a₁)
    : transport (fun x => f x = g x) p q = (ap f p)^-1 @ q @ (ap g p).
  by induction p; exact (concat_1p _)^-1

Definition eq_transport_FlFr_D {B : A -> Type} {f g : forall a, B a}
    (p : a₁ = a₂) (q : f a₁ = g a₁)
      : transport (fun x => f x = g x) p q = (apdt f p)^-1 @ ap (transport B p) q @ (apdt g p).
  by induction p; exact !ap_id^-1 @ (concat_1p _)^-1

Definition eq_transport_FFlr (p : a₁ = a₂) (q : h (f a₁) = a₁)
    : transport (fun x => h (f x) = x) p q = (ap h (ap f p))^-1 @ q @ p.
  by induction p; exact (concat_1p _)^-1

Definition eq_transport_lFFr (p : a₁ = a₂) (q : a₁ = h (f a₁))
    : transport (fun x => x = h (f x)) p q = p^-1 @ q @ (ap h (ap f p)).
  by induction p; exact (concat_1p _)^-1

  (* Pathovers *)

  (* In the comment we give the fibration of the pathover *)

  (* we should probably try to do everything just with pathover_eq (defined in cubical.square), *)

Definition eq_pathover_l (p : a₁ = a₂) (q : a₁ = a₃) : q =[p] p^-1 @ q . (*(fun x => x = a₃)*)
  by induction p; induction q; exact idpo

Definition eq_pathover_r (p : a₂ = a₃) (q : a₁ = a₂) : q =[p] q @ p . (*(fun x => a₁ = x)*)
  by induction p; induction q; exact idpo

Definition eq_pathover_lr (p : a₁ = a₂) (q : a₁ = a₁) : q =[p] p^-1 @ q @ p . (*(fun x => x = x)*)
  by induction p; rewrite [▸*,idp_con]; exact idpo

Definition eq_pathover_Fl (p : a₁ = a₂) (q : f a₁ = b) : q =[p] (ap f p)^-1 @ q . (*(fun x => f x = b)*)
  by induction p; induction q; exact idpo

Definition eq_pathover_Fl' (p : a₁ = a₂) (q : f a₂ = b) : (ap f p) @ q =[p] q . (*(fun x => f x = b)*)
  by induction p; induction q; exact idpo


Definition eq_pathover_Fr (p : a₁ = a₂) (q : b = f a₁) : q =[p] q @ (ap f p) . (*(fun x => b = f x)*)
  by induction p; exact idpo

Definition eq_pathover_FlFr (p : a₁ = a₂) (q : f a₁ = g a₁) : q =[p] (ap f p)^-1 @ q @ (ap g p).
  (*(fun x => f x = g x)*)
  by induction p; rewrite [▸*,idp_con]; exact idpo

Definition eq_pathover_FlFr_D {B : A -> Type} {f g : forall a, B a} (p : a₁ = a₂) (q : f a₁ = g a₁)
    : q =[p] (apdt f p)^-1 @ ap (transport B p) q @ (apdt g p) . (*(fun x => f x = g x)*)
  by induction p; rewrite [▸*,idp_con,ap_id];exact idpo

Definition eq_pathover_FFlr (p : a₁ = a₂) (q : h (f a₁) = a₁) : q =[p] (ap h (ap f p))^-1 @ q @ p.
  (*(fun x => h (f x) = x)*)
  by induction p; rewrite [▸*,idp_con];exact idpo

Definition eq_pathover_lFFr (p : a₁ = a₂) (q : a₁ = h (f a₁)) : q =[p] p^-1 @ q @ (ap h (ap f p)).
  (*(fun x => x = h (f x))*)
  by induction p; rewrite [▸*,idp_con];exact idpo

Definition eq_pathover_r_idp (p : a₁ = a₂) : idp =[p] p . (*(fun x => a₁ = x)*)
  by induction p; exact idpo

Definition eq_pathover_l_idp (p : a₁ = a₂) : idp =[p] p^-1 . (*(fun x => x = a₁)*)
  by induction p; exact idpo

Definition eq_pathover_l_idp' (p : a₁ = a₂) : idp =[p^-1] p . (*(fun x => x = a₂)*)
  by induction p; exact idpo

  (* The Functorial action of paths is [ap]. *)

  (* Equivalences between path spaces *)

  (* [is_equiv_ap] is in init.equiv  *)

Definition equiv_ap (f : A -> B) [H : is_equiv f] (a₁ a₂ : A)
    : (a₁ = a₂) <~> (f a₁ = f a₂).
  equiv.mk (ap f) _

  (* Path operations are equivalences *)

Definition is_equiv_eq_inverse (a₁ a₂ : A)
    : is_equiv (inverse : a₁ = a₂ -> a₂ = a₁).
  is_equiv.mk inverse inverse inv_inv inv_inv (fun p => eq.rec_on p idp)
  local attribute is_equiv_eq_inverse [instance]

Definition eq_equiv_eq_symm (a₁ a₂ : A) : (a₁ = a₂) <~> (a₂ = a₁).
  equiv.mk inverse _

Definition is_equiv_concat_left [instance] (p : a₁ = a₂) (a₃ : A)
    : is_equiv (concat p : a₂ = a₃ -> a₁ = a₃).
  is_equiv.mk (concat p) (concat p^-1)
              (con_inv_cancel_left p)
              (inv_con_cancel_left p)
              abstract (fun q => by induction p;induction q;reflexivity) end
  local attribute is_equiv_concat_left [instance]

Definition equiv_eq_closed_left (a₃ : A) (p : a₁ = a₂) : (a₁ = a₃) <~> (a₂ = a₃).
  equiv.mk (concat p^-1) _

Definition is_equiv_concat_right [instance] (p : a₂ = a₃) (a₁ : A)
    : is_equiv (fun q : a₁ = a₂ => q @ p).
  is_equiv.mk (fun q => q @ p) (fun q => q @ p^-1)
              (fun q => inv_con_cancel_right q p)
              (fun q => con_inv_cancel_right q p)
              (fun q => by induction p;induction q;reflexivity)
  local attribute is_equiv_concat_right [instance]

Definition equiv_eq_closed_right (a₁ : A) (p : a₂ = a₃) : (a₁ = a₂) <~> (a₁ = a₃).
  equiv.mk (fun q => q @ p) _

Definition eq_equiv_eq_closed (p : a₁ = a₂) (q : a₃ = a₄) : (a₁ = a₃) <~> (a₂ = a₄).
  equiv.trans (equiv_eq_closed_left a₃ p) (equiv_eq_closed_right a₂ q)

Definition loop_equiv_eq_closed {A : Type} {a a' : A} (p : a = a')
    : (a = a) <~> (a' = a').
  eq_equiv_eq_closed p p

Definition is_equiv_whisker_left (p : a₁ = a₂) (q r : a₂ = a₃)
  : is_equiv (whisker_left p : q = r -> p @ q = p @ r).
Proof.
  fapply adjointify,
    {intro s, apply (!cancel_left s)},
    {intro s,
      apply concat, {apply whisker_left_con_right},
      apply concat, rotate_left 1, apply (whisker_left_inv_left p s),
      apply concat2,
        {apply concat, {apply whisker_left_con_right},
          apply concat2,
            {induction p, induction q, reflexivity},
            {reflexivity}},
        {induction p, induction r, reflexivity}},
    {intro s, induction s, induction q, induction p, reflexivity}
Defined.

Definition eq_equiv_con_eq_con_left (p : a₁ = a₂) (q r : a₂ = a₃)
    : (q = r) <~> (p @ q = p @ r).
  equiv.mk _ !is_equiv_whisker_left

Definition is_equiv_whisker_right {p q : a₁ = a₂} (r : a₂ = a₃)
    : is_equiv (fun s => whisker_right r s : p = q -> p @ r = q @ r).
Proof.
  fapply adjointify,
    {intro s, apply (!cancel_right s)},
    {intro s, induction r, cases s, induction q, reflexivity},
    {intro s, induction s, induction r, induction p, reflexivity}
Defined.

Definition eq_equiv_con_eq_con_right (p q : a₁ = a₂) (r : a₂ = a₃)
    : (p = q) <~> (p @ r = q @ r).
  equiv.mk _ !is_equiv_whisker_right

  (*
    The following proofs can be simplified a bit by concatenating previous equivalences.
    However, these proofs have the advantage that the inverse isDefinitionally equal to
    what we would expect
  *)
Definition is_equiv_con_eq_of_eq_inv_con (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (con_eq_of_eq_inv_con : p = r^-1 @ q -> r @ p = q).
Proof.
    fapply adjointify,
    { apply eq_inv_con_of_con_eq},
    { intro s, induction r, rewrite [↑[con_eq_of_eq_inv_con,eq_inv_con_of_con_eq],
        con.assoc,con.assoc,con.left_inv,▸*,-con.assoc,con.right_inv,▸* at *,idp_con s]},
    { intro s, induction r, rewrite [↑[con_eq_of_eq_inv_con,eq_inv_con_of_con_eq],
        con.assoc,con.assoc,con.right_inv,▸*,-con.assoc,con.left_inv,▸* at *,idp_con s] },
Defined.

Definition eq_inv_con_equiv_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : (p = r^-1 @ q) <~> (r @ p = q).
  equiv.mk _ !is_equiv_con_eq_of_eq_inv_con

Definition is_equiv_con_eq_of_eq_con_inv (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (con_eq_of_eq_con_inv : r = q @ p^-1 -> r @ p = q).
Proof.
    fapply adjointify,
    { apply eq_con_inv_of_con_eq},
    { intro s, induction p, rewrite [↑[con_eq_of_eq_con_inv,eq_con_inv_of_con_eq]]},
    { intro s, induction p, rewrite [↑[con_eq_of_eq_con_inv,eq_con_inv_of_con_eq]] },
Defined.

Definition eq_con_inv_equiv_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : (r = q @ p^-1) <~> (r @ p = q).
  equiv.mk _ !is_equiv_con_eq_of_eq_con_inv

Definition is_equiv_inv_con_eq_of_eq_con (p : a₁ = a₃) (q : a₂ = a₃) (r : a₁ = a₂)
    : is_equiv (inv_con_eq_of_eq_con : p = r @ q -> r^-1 @ p = q).
Proof.
    fapply adjointify,
    { apply eq_con_of_inv_con_eq},
    { intro s, induction r, rewrite [↑[inv_con_eq_of_eq_con,eq_con_of_inv_con_eq],
        con.assoc,con.assoc,con.left_inv,▸*,-con.assoc,con.right_inv,▸* at *,idp_con s]},
    { intro s, induction r, rewrite [↑[inv_con_eq_of_eq_con,eq_con_of_inv_con_eq],
        con.assoc,con.assoc,con.right_inv,▸*,-con.assoc,con.left_inv,▸* at *,idp_con s] },
Defined.

Definition eq_con_equiv_inv_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₁ = a₂)
    : (p = r @ q) <~> (r^-1 @ p = q).
  equiv.mk _ !is_equiv_inv_con_eq_of_eq_con

Definition is_equiv_con_inv_eq_of_eq_con (p : a₃ = a₁) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (con_inv_eq_of_eq_con : r = q @ p -> r @ p^-1 = q).
Proof.
    fapply adjointify,
    { apply eq_con_of_con_inv_eq},
    { intro s, induction p, rewrite [↑[con_inv_eq_of_eq_con,eq_con_of_con_inv_eq]]},
    { intro s, induction p, rewrite [↑[con_inv_eq_of_eq_con,eq_con_of_con_inv_eq]] },
Defined.

Definition eq_con_equiv_con_inv_eq (p : a₃ = a₁) (q : a₂ = a₃) (r : a₂ = a₁)
    : (r = q @ p) <~> (r @ p^-1 = q).
   equiv.mk _ !is_equiv_con_inv_eq_of_eq_con

  local attribute is_equiv_inv_con_eq_of_eq_con
                  is_equiv_con_inv_eq_of_eq_con
                  is_equiv_con_eq_of_eq_con_inv
                  is_equiv_con_eq_of_eq_inv_con [instance]

Definition is_equiv_eq_con_of_inv_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (eq_con_of_inv_con_eq : r^-1 @ q = p -> q = r @ p).
  is_equiv_inv inv_con_eq_of_eq_con

Definition is_equiv_eq_con_of_con_inv_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (eq_con_of_con_inv_eq : q @ p^-1 = r -> q = r @ p).
  is_equiv_inv con_inv_eq_of_eq_con

Definition is_equiv_eq_con_inv_of_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (eq_con_inv_of_con_eq : r @ p = q -> r = q @ p^-1).
  is_equiv_inv con_eq_of_eq_con_inv

Definition is_equiv_eq_inv_con_of_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (eq_inv_con_of_con_eq : r @ p = q -> p = r^-1 @ q).
  is_equiv_inv con_eq_of_eq_inv_con

Definition is_equiv_con_inv_eq_idp (p q : a₁ = a₂)
    : is_equiv (con_inv_eq_idp : p = q -> p @ q^-1 = idp).
Proof.
    fapply adjointify,
    { apply eq_of_con_inv_eq_idp},
    { intro s, induction q, esimp at *, cases s, reflexivity},
    { intro s, induction s, induction p, reflexivity},
Defined.

Definition is_equiv_inv_con_eq_idp (p q : a₁ = a₂)
    : is_equiv (inv_con_eq_idp : p = q -> q^-1 @ p = idp).
Proof.
    fapply adjointify,
    { apply eq_of_inv_con_eq_idp},
    { intro s, induction q, esimp [eq_of_inv_con_eq_idp] at *,
      eapply is_equiv_rect (eq_equiv_con_eq_con_left idp p idp), clear s,
      intro s, cases s, reflexivity},
    { intro s, induction s, induction p, reflexivity},
Defined.

Definition eq_equiv_con_inv_eq_idp (p q : a₁ = a₂) : (p = q) <~> (p @ q^-1 = idp).
  equiv.mk _ !is_equiv_con_inv_eq_idp

Definition eq_equiv_inv_con_eq_idp (p q : a₁ = a₂) : (p = q) <~> (q^-1 @ p = idp).
  equiv.mk _ !is_equiv_inv_con_eq_idp

  (* Pathover Equivalences *)

Definition eq_pathover_equiv_l (p : a₁ = a₂) (q : a₁ = a₃) (r : a₂ = a₃) : q =[p] r <~> q = p @ r.
  (*(fun x => x = a₃)*)
  by induction p; exact !pathover_idp @e !equiv_eq_closed_right (concat_1p _)^-1

Definition eq_pathover_equiv_r (p : a₂ = a₃) (q : a₁ = a₂) (r : a₁ = a₃) : q =[p] r <~> q @ p = r.
  (*(fun x => a₁ = x)*)
  by induction p; apply pathover_idp

Definition eq_pathover_equiv_lr (p : a₁ = a₂) (q : a₁ = a₁) (r : a₂ = a₂)
    : q =[p] r <~> q @ p = p @ r . (*(fun x => x = x)*)
  by induction p; exact !pathover_idp @e !equiv_eq_closed_right (concat_1p _)^-1

Definition eq_pathover_equiv_Fl (p : a₁ = a₂) (q : f a₁ = b) (r : f a₂ = b)
    : q =[p] r <~> q = ap f p @ r . (*(fun x => f x = b)*)
  by induction p; exact !pathover_idp @e !equiv_eq_closed_right (concat_1p _)^-1

Definition eq_pathover_equiv_Fr (p : a₁ = a₂) (q : b = f a₁) (r : b = f a₂)
    : q =[p] r <~> q @ ap f p = r . (*(fun x => b = f x)*)
  by induction p; apply pathover_idp

Definition eq_pathover_equiv_FlFr (p : a₁ = a₂) (q : f a₁ = g a₁) (r : f a₂ = g a₂)
    : q =[p] r <~> q @ ap g p = ap f p @ r . (*(fun x => f x = g x)*)
  by induction p; exact !pathover_idp @e !equiv_eq_closed_right (concat_1p _)^-1

Definition eq_pathover_equiv_FFlr (p : a₁ = a₂) (q : h (f a₁) = a₁) (r : h (f a₂) = a₂)
    : q =[p] r <~> q @ p = ap h (ap f p) @ r.
  (*(fun x => h (f x) = x)*)
  by induction p; exact !pathover_idp @e !equiv_eq_closed_right (concat_1p _)^-1

Definition eq_pathover_equiv_lFFr (p : a₁ = a₂) (q : a₁ = h (f a₁)) (r : a₂ = h (f a₂))
    : q =[p] r <~> q @ ap h (ap f p) = p @ r.
  (*(fun x => x = h (f x))*)
  by induction p; exact !pathover_idp @e !equiv_eq_closed_right (concat_1p _)^-1

  (* a lot of this library still needs to be ported from Coq HoTT *)

  (* the behavior of equality in other types is described in the corresponding type files *)

  (* encode decode method *)

  open is_trunc
Definition encode_decode_method' (a₀ a : A) (code : A -> Type) (c₀ : code a₀)
    (decode : forall (a : A) (c : code a), a₀ = a)
    (encode_decode : forall (a : A) (c : code a), c₀ =[decode a c] c)
    (decode_encode : decode a₀ c₀ = idp) : (a₀ = a) <~> code a.
Proof.
    fapply equiv.MK,
    { intro p, exact p # c₀},
    { apply decode},
    { intro c, apply tr_eq_of_pathover, apply encode_decode},
    { intro p, induction p, apply decode_encode},
Defined.

Defined.

  section
    parameters {A : Type} (a₀ : A) (code : A -> Type) (H : is_contr (Σa, code a))
      (p : (center (Σa, code a)).1 = a₀)
    include p
    protectedDefinition encode {a : A} (q : a₀ = a) : code a.
    (p @ q) # (center (Σa, code a)).2

    protectedDefinition decode' {a : A} (c : code a) : a₀ = a.
    (is_prop.elim ⟨a₀, encode idp⟩ ⟨a, c⟩)..1

    protectedDefinition decode {a : A} (c : code a) : a₀ = a.
    (decode' (encode idp))^-1 @ decode' c

Definition total_space_method (a : A) : (a₀ = a) <~> code a.
    begin
      fapply equiv.MK,
      { exact encode},
      { exact decode},
      { intro c,
        unfold [encode, decode, decode'],
        induction p, esimp, rewrite [is_prop_elim_self,▸*,+idp_con],
        apply tr_eq_of_pathover,
        eapply @sigma.rec_on _ _ (fun x => x.2 =[(is_prop.elim ⟨x.1, x.2⟩ ⟨a, c⟩)..1] c)
          (center (sigma code)),
        intro a c, apply eq_pr2},
      { intro q, induction q, esimp, apply con.left_inv, },
    end
Defined.

Definition encode_decode_method {A : Type} (a₀ a : A) (code : A -> Type) (c₀ : code a₀)
    (decode : forall (a : A) (c : code a), a₀ = a)
    (encode_decode : forall (a : A) (c : code a), c₀ =[decode a c] c) : (a₀ = a) <~> code a.
Proof.
    fapply total_space_method,
    { fapply @is_contr.mk,
      { exact ⟨a₀, c₀⟩},
      { intro p, fapply sigma_eq,
          apply decode, exact p.2,
        apply encode_decode}},
    { reflexivity}
Defined.

Defined. eq
