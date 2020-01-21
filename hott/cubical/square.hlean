(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Squares in a type
*)
import types.eq
open eq equiv is_equiv sigma

namespace eq

  variables {A B C : Type} {a a' a'' a₀₀ a₂₀ a₄₀ a₀₂ a₂₂ a₂₄ a₀₄ a₄₂ a₄₄ a₁ a₂ a₃ a₄ : A}
  (*a₀₀*) {p₁₀ p₁₀' : a₀₀ = a₂₀} (*a₂₀*) {p₃₀ : a₂₀ = a₄₀} (*a₄₀*)
  {p₀₁ p₀₁' : a₀₀ = a₀₂} (*s₁₁*) {p₂₁ p₂₁' : a₂₀ = a₂₂} (*s₃₁*) {p₄₁ : a₄₀ = a₄₂}
  (*a₀₂*) {p₁₂ p₁₂' : a₀₂ = a₂₂} (*a₂₂*) {p₃₂ : a₂₂ = a₄₂} (*a₄₂*)
  {p₀₃ : a₀₂ = a₀₄} (*s₁₃*) {p₂₃ : a₂₂ = a₂₄} (*s₃₃*) {p₄₃ : a₄₂ = a₄₄}
  (*a₀₄*) {p₁₄ : a₀₄ = a₂₄} (*a₂₄*) {p₃₄ : a₂₄ = a₄₄} (*a₄₄*)
  {b : B} {c : C}

  inductive square {A : Type} {a₀₀ : A}
  : forall {a₂₀ a₀₂ a₂₂ : A}, a₀₀ = a₂₀ -> a₀₂ = a₂₂ -> a₀₀ = a₀₂ -> a₂₀ = a₂₂ -> Type.
  ids : square idp idp idp idp
  (* square top bottom left right *)

  variables {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁} {s₃₁ : square p₃₀ p₃₂ p₂₁ p₄₁}
  {s₁₃ : square p₁₂ p₁₄ p₀₃ p₂₃} {s₃₃ : square p₃₂ p₃₄ p₂₃ p₄₃}

Definition ids              . @square.ids
Definition idsquare (a : A) . @square.ids A a

Definition hrefl (p : a = a') : square idp idp p p.
  by induction p; exact ids

Definition vrefl (p : a = a') : square p p idp idp.
  by induction p; exact ids

Definition hrfl {p : a = a'} : square idp idp p p.
  !hrefl
Definition vrfl {p : a = a'} : square p p idp idp.
  !vrefl

Definition hdeg_square {p q : a = a'} (r : p = q) : square idp idp p q.
  by induction r;apply hrefl

Definition vdeg_square {p q : a = a'} (r : p = q) : square p q idp idp.
  by induction r;apply vrefl

Definition hdeg_square_idp (p : a = a') : hdeg_square (refl p) = hrfl.
  by reflexivity

Definition vdeg_square_idp (p : a = a') : vdeg_square (refl p) = vrfl.
  by reflexivity

Definition hconcat [unfold 16] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (s₃₁ : square p₃₀ p₃₂ p₂₁ p₄₁)
  : square (p₁₀ @ p₃₀) (p₁₂ @ p₃₂) p₀₁ p₄₁.
  by induction s₃₁; exact s₁₁

Definition vconcat [unfold 16] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (s₁₃ : square p₁₂ p₁₄ p₀₃ p₂₃)
  : square p₁₀ p₁₄ (p₀₁ @ p₀₃) (p₂₁ @ p₂₃).
  by induction s₁₃; exact s₁₁

Definition dconcat [unfold 14] {p₀₀ : a₀₀ = a} {p₂₂ : a = a₂₂}
  (s₂₁ : square p₀₀ p₁₂ p₀₁ p₂₂) (s₁₂ : square p₁₀ p₂₂ p₀₀ p₂₁) : square p₁₀ p₁₂ p₀₁ p₂₁.
  by induction s₁₂; exact s₂₁

Definition hinverse [unfold 10] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₀^-1 p₁₂^-1 p₂₁ p₀₁.
  by induction s₁₁;exact ids

Definition vinverse [unfold 10] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₂ p₁₀ p₀₁^-1 p₂₁^-1.
  by induction s₁₁;exact ids

Definition eq_vconcat [unfold 11] {p : a₀₀ = a₂₀} (r : p = p₁₀) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) :
  square p p₁₂ p₀₁ p₂₁.
  by induction r; exact s₁₁

Definition vconcat_eq [unfold 12] {p : a₀₂ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₁₂ = p) :
  square p₁₀ p p₀₁ p₂₁.
  by induction r; exact s₁₁

Definition eq_hconcat [unfold 11] {p : a₀₀ = a₀₂} (r : p = p₀₁) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) :
  square p₁₀ p₁₂ p p₂₁.
  by induction r; exact s₁₁

Definition hconcat_eq [unfold 12] {p : a₂₀ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁ = p) :
  square p₁₀ p₁₂ p₀₁ p.
  by induction r; exact s₁₁

  infix ` @h `:69 . hconcat --type using \tr
  infix ` @v `:70 . vconcat --type using \tr
  infixl ` @hp `:71 . hconcat_eq --type using \tr
  infixl ` @vp `:73 . vconcat_eq --type using \tr
  infixr ` @ph `:72 . eq_hconcat --type using \tr
  infixr ` @pv `:74 . eq_vconcat --type using \tr
  postfix `^-1ʰ`:(max+1) . hinverse --type using \-1h
  postfix `^-1ᵛ`:(max+1) . vinverse --type using \-1v

Definition transpose [unfold 10] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₀₁ p₂₁ p₁₀ p₁₂.
  by induction s₁₁;exact ids

Definition aps [unfold 12] (f : A -> B) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : square (ap f p₁₀) (ap f p₁₂) (ap f p₀₁) (ap f p₂₁).
  by induction s₁₁;exact ids

  (* canceling, whiskering and moving thinks along the sides of the square *)
Definition whisker_tl (p : a = a₀₀) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : square (p @ p₁₀) p₁₂ (p @ p₀₁) p₂₁.
  by induction s₁₁;induction p;constructor

Definition whisker_br (p : a₂₂ = a) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : square p₁₀ (p₁₂ @ p) p₀₁ (p₂₁ @ p).
  by induction p;exact s₁₁

Definition whisker_rt (p : a = a₂₀) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : square (p₁₀ @ p^-1) p₁₂ p₀₁ (p @ p₂₁).
  by induction s₁₁;induction p;constructor

Definition whisker_tr (p : a₂₀ = a) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : square (p₁₀ @ p) p₁₂ p₀₁ (p^-1 @ p₂₁).
  by induction s₁₁;induction p;constructor

Definition whisker_bl (p : a = a₀₂) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : square p₁₀ (p @ p₁₂) (p₀₁ @ p^-1) p₂₁.
  by induction s₁₁;induction p;constructor

Definition whisker_lb (p : a₀₂ = a) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : square p₁₀ (p^-1 @ p₁₂) (p₀₁ @ p) p₂₁.
  by induction s₁₁;induction p;constructor

Definition cancel_tl (p : a = a₀₀) (s₁₁ : square (p @ p₁₀) p₁₂ (p @ p₀₁) p₂₁)
  : square p₁₀ p₁₂ p₀₁ p₂₁.
  by induction p; rewrite +idp_con at s₁₁; exact s₁₁

Definition cancel_br (p : a₂₂ = a) (s₁₁ : square p₁₀ (p₁₂ @ p) p₀₁ (p₂₁ @ p))
  : square p₁₀ p₁₂ p₀₁ p₂₁.
  by induction p;exact s₁₁

Definition cancel_rt (p : a = a₂₀) (s₁₁ : square (p₁₀ @ p^-1) p₁₂ p₀₁ (p @ p₂₁))
  : square p₁₀ p₁₂ p₀₁ p₂₁.
  by induction p; rewrite idp_con at s₁₁; exact s₁₁

Definition cancel_tr (p : a₂₀ = a) (s₁₁ : square (p₁₀ @ p) p₁₂ p₀₁ (p^-1 @ p₂₁))
  : square p₁₀ p₁₂ p₀₁ p₂₁.
  by induction p; rewrite [▸* at s₁₁,idp_con at s₁₁]; exact s₁₁

Definition cancel_bl (p : a = a₀₂) (s₁₁ : square p₁₀ (p @ p₁₂) (p₀₁ @ p^-1) p₂₁)
  : square p₁₀ p₁₂ p₀₁ p₂₁.
  by induction p; rewrite idp_con at s₁₁; exact s₁₁

Definition cancel_lb (p : a₀₂ = a) (s₁₁ : square p₁₀ (p^-1 @ p₁₂) (p₀₁ @ p) p₂₁)
  : square p₁₀ p₁₂ p₀₁ p₂₁.
  by induction p; rewrite [▸* at s₁₁,idp_con at s₁₁]; exact s₁₁

Definition move_top_of_left   {p : a₀₀ = a} {q : a = a₀₂} (s : square p₁₀ p₁₂ (p @ q) p₂₁)
  : square (p^-1 @ p₁₀) p₁₂ q p₂₁.
  by apply cancel_tl p; rewrite con_inv_cancel_left; exact s

Definition move_top_of_left'  {p : a = a₀₀} {q : a = a₀₂} (s : square p₁₀ p₁₂ (p^-1 @ q) p₂₁)
  : square (p @ p₁₀) p₁₂ q p₂₁.
  by apply cancel_tl p^-1; rewrite inv_con_cancel_left; exact s

Definition move_left_of_top   {p : a₀₀ = a} {q : a = a₂₀} (s : square (p @ q) p₁₂ p₀₁ p₂₁)
  : square q p₁₂ (p^-1 @ p₀₁) p₂₁.
  by apply cancel_tl p; rewrite con_inv_cancel_left; exact s

Definition move_left_of_top'  {p : a = a₀₀} {q : a = a₂₀} (s : square (p^-1 @ q) p₁₂ p₀₁ p₂₁)
  : square q p₁₂ (p @ p₀₁) p₂₁.
  by apply cancel_tl p^-1; rewrite inv_con_cancel_left; exact s

Definition move_bot_of_right  {p : a₂₀ = a} {q : a = a₂₂} (s : square p₁₀ p₁₂ p₀₁ (p @ q))
  : square p₁₀ (p₁₂ @ q^-1) p₀₁ p.
  by apply cancel_br q; rewrite inv_con_cancel_right; exact s

Definition move_bot_of_right' {p : a₂₀ = a} {q : a₂₂ = a} (s : square p₁₀ p₁₂ p₀₁ (p @ q^-1))
  : square p₁₀ (p₁₂ @ q) p₀₁ p.
  by apply cancel_br q^-1; rewrite con_inv_cancel_right; exact s

Definition move_right_of_bot  {p : a₀₂ = a} {q : a = a₂₂} (s : square p₁₀ (p @ q) p₀₁ p₂₁)
  : square p₁₀ p p₀₁ (p₂₁ @ q^-1).
  by apply cancel_br q; rewrite inv_con_cancel_right; exact s

Definition move_right_of_bot' {p : a₀₂ = a} {q : a₂₂ = a} (s : square p₁₀ (p @ q^-1) p₀₁ p₂₁)
  : square p₁₀ p p₀₁ (p₂₁ @ q).
  by apply cancel_br q^-1; rewrite con_inv_cancel_right; exact s

Definition move_top_of_right  {p : a₂₀ = a} {q : a = a₂₂} (s : square p₁₀ p₁₂ p₀₁ (p @ q))
  : square (p₁₀ @ p) p₁₂ p₀₁ q.
  by apply cancel_rt p; rewrite con_inv_cancel_right; exact s

Definition move_right_of_top  {p : a₀₀ = a} {q : a = a₂₀} (s : square (p @ q) p₁₂ p₀₁ p₂₁)
  : square p p₁₂ p₀₁ (q @ p₂₁).
  by apply cancel_tr q; rewrite inv_con_cancel_left; exact s

Definition move_bot_of_left   {p : a₀₀ = a} {q : a = a₀₂} (s : square p₁₀ p₁₂ (p @ q) p₂₁)
  : square  p₁₀ (q @ p₁₂) p p₂₁.
  by apply cancel_lb q; rewrite inv_con_cancel_left; exact s

Definition move_left_of_bot   {p : a₀₂ = a} {q : a = a₂₂} (s : square p₁₀ (p @ q) p₀₁ p₂₁)
  : square p₁₀ q (p₀₁ @ p) p₂₁.
  by apply cancel_bl p; rewrite con_inv_cancel_right; exact s

  (* some higher ∞-groupoid operations *)

Definition vconcat_vrfl (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : s₁₁ @v vrefl p₁₂ = s₁₁.
  by induction s₁₁; reflexivity

Definition hconcat_hrfl (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : s₁₁ @h hrefl p₂₁ = s₁₁.
  by induction s₁₁; reflexivity

  (* equivalences *)

Definition eq_of_square [unfold 10] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : p₁₀ @ p₂₁ = p₀₁ @ p₁₂.
  by induction s₁₁; apply idp

Definition square_of_eq (r : p₁₀ @ p₂₁ = p₀₁ @ p₁₂) : square p₁₀ p₁₂ p₀₁ p₂₁.
  by induction p₁₂; esimp at r; induction r; induction p₂₁; induction p₁₀; exact ids

Definition eq_top_of_square [unfold 10] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : p₁₀ = p₀₁ @ p₁₂ @ p₂₁^-1.
  by induction s₁₁; apply idp

Definition square_of_eq_top (r : p₁₀ = p₀₁ @ p₁₂ @ p₂₁^-1) : square p₁₀ p₁₂ p₀₁ p₂₁.
  by induction p₂₁; induction p₁₂; esimp at r;induction r;induction p₁₀;exact ids

Definition eq_bot_of_square [unfold 10] (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : p₁₂ = p₀₁^-1 @ p₁₀ @ p₂₁.
  by induction s₁₁; apply idp

Definition square_of_eq_bot (r : p₀₁^-1 @ p₁₀ @ p₂₁ = p₁₂) : square p₁₀ p₁₂ p₀₁ p₂₁.
  by induction p₂₁; induction p₁₀; esimp at r; induction r; induction p₀₁; exact ids

Definition square_equiv_eq (t : a₀₀ = a₀₂) (b : a₂₀ = a₂₂)
  (l : a₀₀ = a₂₀) (r : a₀₂ = a₂₂) : square t b l r <~> t @ r = l @ b.
Proof.
  fapply equiv.MK,
  { exact eq_of_square},
  { exact square_of_eq},
  { intro s, induction b, esimp [concat] at s, induction s, induction r, induction t, apply idp},
  { intro s, induction s, apply idp},
Defined.

Definition hdeg_square_equiv' (p q : a = a') : square idp idp p q <~> p = q.
  by transitivity _;apply square_equiv_eq;transitivity _;apply eq_equiv_eq_symm;
  apply equiv_eq_closed_right;apply idp_con

Definition vdeg_square_equiv' (p q : a = a') : square p q idp idp <~> p = q.
  by transitivity _;apply square_equiv_eq;apply equiv_eq_closed_right; apply idp_con

Definition eq_of_hdeg_square {p q : a = a'} (s : square idp idp p q) : p = q.
  to_fun !hdeg_square_equiv' s

Definition eq_of_vdeg_square {p q : a = a'} (s : square p q idp idp) : p = q.
  to_fun !vdeg_square_equiv' s

Definition top_deg_square (l : a₁ = a₂) (b : a₂ = a₃) (r : a₄ = a₃)
  : square (l @ b @ r^-1) b l r.
  by induction r;induction b;induction l;constructor

Definition bot_deg_square (l : a₁ = a₂) (t : a₁ = a₃) (r : a₃ = a₄)
  : square t (l^-1 @ t @ r) l r.
  by induction r;induction t;induction l;constructor

  (*
  the following two equivalences have as underlying inverse function the functions
  hdeg_square and vdeg_square, respectively.
  See example below theDefinition
  *)
Definition hdeg_square_equiv (p q : a = a') :
  square idp idp p q <~> p = q.
Proof.
  fapply equiv_change_fun =>
  { fapply equiv_change_inv, apply hdeg_square_equiv', exact hdeg_square,
  intro s, induction s, induction p, reflexivity},
  { exact eq_of_hdeg_square},
  { reflexivity}
Defined.

Definition vdeg_square_equiv (p q : a = a') :
  square p q idp idp <~> p = q.
Proof.
  fapply equiv_change_fun =>
  { fapply equiv_change_inv, apply vdeg_square_equiv',exact vdeg_square,
  intro s, induction s, induction p, reflexivity},
  { exact eq_of_vdeg_square},
  { reflexivity}
Defined.

  example (p q : a = a') : to_inv (hdeg_square_equiv p q) = hdeg_square . idp

  (*
  characterization of pathovers in a equality type. The type B of the equality is fixed here.
  A version where B may also varies over the path p is given in the file squareover
  *)

Definition eq_pathover {f g : A -> B} {p : a = a'} {q : f a = g a} {r : f a' = g a'}
  (s : square q r (ap f p) (ap g p)) : q =[p] r.
Proof. induction p, apply pathover_idp_of_eq, exact eq_of_vdeg_square s end

Definition eq_pathover_constant_left {g : A -> B} {p : a = a'} {b : B} {q : b = g a} {r : b = g a'}
  (s : square q r idp (ap g p)) : q =[p] r.
  eq_pathover (ap_constant p b @ph s)

Definition eq_pathover_id_left {g : A -> A} {p : a = a'} {q : a = g a} {r : a' = g a'}
  (s : square q r p (ap g p)) : q =[p] r.
  eq_pathover (ap_id p @ph s)

Definition eq_pathover_constant_right {f : A -> B} {p : a = a'} {b : B} {q : f a = b} {r : f a' = b}
  (s : square q r (ap f p) idp) : q =[p] r.
  eq_pathover (s @hp (ap_constant p b)^-1)

Definition eq_pathover_id_right {f : A -> A} {p : a = a'} {q : f a = a} {r : f a' = a'}
  (s : square q r (ap f p) p) : q =[p] r.
  eq_pathover (s @hp (ap_id p)^-1)

Definition square_of_pathover [unfold 7]
  {f g : A -> B} {p : a = a'} {q : f a = g a} {r : f a' = g a'}
  (s : q =[p] r) : square q r (ap f p) (ap g p).
  by induction p;apply vdeg_square;exact eq_of_pathover_idp s

Definition eq_pathover_constant_left_id_right {p : a = a'} {a₀ : A} {q : a₀ = a} {r : a₀ = a'}
  (s : square q r idp p) : q =[p] r.
  eq_pathover (ap_constant p a₀ @ph s @hp (ap_id p)^-1)

Definition eq_pathover_id_left_constant_right {p : a = a'} {a₀ : A} {q : a = a₀} {r : a' = a₀}
  (s : square q r p idp) : q =[p] r.
  eq_pathover (ap_id p @ph s @hp (ap_constant p a₀)^-1)

Definition loop_pathover {p : a = a'} {q : a = a} {r : a' = a'} (s : square q r p p) : q =[p] r.
  eq_pathover (ap_id p @ph s @hp (ap_id p)^-1)

  (* interaction of equivalences with operations on squares *)

Definition eq_pathover_equiv_square {f g : A -> B}
  (p : a = a') (q : f a = g a) (r : f a' = g a') : q =[p] r <~> square q r (ap f p) (ap g p).
  equiv.MK square_of_pathover
  eq_pathover
Proof.
  intro s, induction p, esimp [square_of_pathover,eq_pathover],
  exact ap vdeg_square (to_right_inv !pathover_idp (eq_of_vdeg_square s))
  @ to_left_inv !vdeg_square_equiv s
Defined.
Proof.
  intro s, induction p, esimp [square_of_pathover,eq_pathover],
  exact ap pathover_idp_of_eq (to_right_inv !vdeg_square_equiv (eq_of_pathover_idp s))
  @ to_left_inv !pathover_idp s
Defined.

Definition square_of_pathover_eq_concato {f g : A -> B} {p : a = a'} {q q' : f a = g a}
  {r : f a' = g a'} (s' : q = q') (s : q' =[p] r)
  : square_of_pathover (s' @po s) = s' @pv square_of_pathover s.
  by induction s;induction s';reflexivity

Definition square_of_pathover_concato_eq {f g : A -> B} {p : a = a'} {q : f a = g a}
  {r r' : f a' = g a'} (s' : r = r') (s : q =[p] r)
  : square_of_pathover (s @op s') = square_of_pathover s @vp s'.
  by induction s;induction s';reflexivity

Definition square_of_pathover_concato {f g : A -> B} {p : a = a'} {p' : a' = a''} {q : f a = g a}
  {q' : f a' = g a'} {q'' : f a'' = g a''} (s : q =[p] q') (s' : q' =[p'] q'')
  : square_of_pathover (s @o s')
  = ap_con f p p' @ph (square_of_pathover s @v square_of_pathover s') @hp (ap_con g p p')^-1.
  by induction s';induction s;esimp [ap_con,hconcat_eq];exact !vconcat_vrfl^-1

Definition eq_of_square_hrfl (p : a = a') : eq_of_square hrfl = idp_con p.
  by induction p;reflexivity

Definition eq_of_square_vrfl (p : a = a') : eq_of_square vrfl = (idp_con p)^-1.
  by induction p;reflexivity

Definition eq_of_square_hdeg_square {p q : a = a'} (r : p = q)
  : eq_of_square (hdeg_square r) = (concat_1p _) @ r^-1.
  by induction r;induction p;reflexivity

Definition eq_of_square_vdeg_square {p q : a = a'} (r : p = q)
  : eq_of_square (vdeg_square r) = r @ (concat_1p _)^-1.
  by induction r;induction p;reflexivity

Definition eq_of_square_eq_vconcat {p : a₀₀ = a₂₀} (r : p = p₁₀) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : eq_of_square (r @pv s₁₁) = whisker_right p₂₁ r @ eq_of_square s₁₁.
  by induction s₁₁;cases r;reflexivity

Definition eq_of_square_eq_hconcat {p : a₀₀ = a₀₂} (r : p = p₀₁) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  : eq_of_square (r @ph s₁₁) = eq_of_square s₁₁ @ (whisker_right p₁₂ r)^-1.
  by induction r;reflexivity

Definition eq_of_square_vconcat_eq {p : a₀₂ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₁₂ = p)
  : eq_of_square (s₁₁ @vp r) = eq_of_square s₁₁ @ whisker_left p₀₁ r.
  by induction r;reflexivity

Definition eq_of_square_hconcat_eq {p : a₂₀ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁ = p)
  : eq_of_square (s₁₁ @hp r) = (whisker_left p₁₀ r)^-1 @ eq_of_square s₁₁.
  by induction s₁₁; induction r;reflexivity

Definition change_path_eq_pathover {A B : Type} {a a' : A} {f g : A -> B}
  {p p' : a = a'} (r : p = p')
  {q : f a = g a} {q' : f a' = g a'}
  (s : square q q' (ap f p) (ap g p)) :
  change_path r (eq_pathover s) = eq_pathover ((ap02 f r)^-1 @ph s @hp (ap02 g r)).
  by induction r; reflexivity

Definition eq_hconcat_hdeg_square {A : Type} {a a' : A} {p₁ p₂ p₃ : a = a'} (q₁ : p₁ = p₂)
  (q₂ : p₂ = p₃) : q₁ @ph hdeg_square q₂ = hdeg_square (q₁ @ q₂).
  by induction q₁; induction q₂; reflexivity

Definition hdeg_square_hconcat_eq {A : Type} {a a' : A} {p₁ p₂ p₃ : a = a'} (q₁ : p₁ = p₂)
  (q₂ : p₂ = p₃) : hdeg_square q₁ @hp q₂ = hdeg_square (q₁ @ q₂).
  by induction q₁; induction q₂; reflexivity

Definition eq_hconcat_eq_hdeg_square {A : Type} {a a' : A} {p₁ p₂ p₃ p₄ : a = a'} (q₁ : p₁ = p₂)
  (q₂ : p₂ = p₃) (q₃ : p₃ = p₄) : q₁ @ph hdeg_square q₂ @hp q₃ = hdeg_square (q₁ @ q₂ @ q₃).
  by induction q₃; apply eq_hconcat_hdeg_square

  (*Definition vconcat_eq [unfold 11] {p : a₀₂ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₁₂ = p) : *)
  (*   square p₁₀ p p₀₁ p₂₁ . *)
  (* by induction r; exact s₁₁ *)

  (*Definition eq_hconcat [unfold 11] {p : a₀₀ = a₀₂} (r : p = p₀₁) *)
  (*   (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₀ p₁₂ p p₂₁ . *)
  (* by induction r; exact s₁₁ *)

  (*Definition hconcat_eq [unfold 11] {p : a₂₀ = a₂₂} *)
  (*   (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁ = p) : square p₁₀ p₁₂ p₀₁ p . *)
  (* by induction r; exact s₁₁ *)


  (* the followingDefinition is very slow, maybe it's interesting to see why? *)
  (*Definition eq_pathover_equiv_square' {f g : A -> B}(p : a = a') (q : f a = g a) (r : f a' = g a') *)
  (*   : square q r (ap f p) (ap g p) <~> q =[p] r . *)
  (* equiv.MK eq_pathover *)
  (*          square_of_pathover *)
  (*          (fun s => begin *)
  (*                 induction p, rewrite [↑[square_of_pathover,eq_pathover], *)
  (*                   to_right_inv !vdeg_square_equiv (eq_of_pathover_idp s), *)
  (*                   to_left_inv !pathover_idp s] *)
  (*               end) *)
  (*          (fun s => begin *)
  (*                 induction p, rewrite [↑[square_of_pathover,eq_pathover],▸*, *)
  (*                   to_right_inv !(@pathover_idp A) (eq_of_vdeg_square s), *)
  (*                   to_left_inv !vdeg_square_equiv s] *)
  (*               end) *)

  (* recursors for squares where some sides are reflexivity *)

Definition rec_on_b [recursor] {a₀₀ : A}
  {P : forall {a₂₀ a₁₂ : A} {t : a₀₀ = a₂₀} {l : a₀₀ = a₁₂} {r : a₂₀ = a₁₂}, square t idp l r -> Type}
  {a₂₀ a₁₂ : A} {t : a₀₀ = a₂₀} {l : a₀₀ = a₁₂} {r : a₂₀ = a₁₂}
  (s : square t idp l r) (H : P ids) : P s.
  have H2 : P (square_of_eq (eq_of_square s)),
  from eq.rec_on (eq_of_square s : t @ r = l) (by induction r; induction t; exact H),
  left_inv (to_fun !square_equiv_eq) s # H2

Definition rec_on_r [recursor] {a₀₀ : A}
  {P : forall {a₀₂ a₂₁ : A} {t : a₀₀ = a₂₁} {b : a₀₂ = a₂₁} {l : a₀₀ = a₀₂}, square t b l idp -> Type}
  {a₀₂ a₂₁ : A} {t : a₀₀ = a₂₁} {b : a₀₂ = a₂₁} {l : a₀₀ = a₀₂}
  (s : square t b l idp) (H : P ids) : P s.
  let p : l @ b = t . (eq_of_square s)^-1 in
  have H2 : P (square_of_eq (eq_of_square s)^-1^-1),
  from @eq.rec_on _ _ (fun x p => P (square_of_eq p^-1)) _ p (by induction b; induction l; exact H),
  left_inv (to_fun !square_equiv_eq) s # !inv_inv # H2

Definition rec_on_l [recursor] {a₀₁ : A}
  {P : forall {a₂₀ a₂₂ : A} {t : a₀₁ = a₂₀} {b : a₀₁ = a₂₂} {r : a₂₀ = a₂₂},
  square t b idp r -> Type}
  {a₂₀ a₂₂ : A} {t : a₀₁ = a₂₀} {b : a₀₁ = a₂₂} {r : a₂₀ = a₂₂}
  (s : square t b idp r) (H : P ids) : P s.
  let p : t @ r = b . eq_of_square s @ (concat_1p _) in
  have H2 : P (square_of_eq (p @ (concat_1p _)^-1)),
  from eq.rec_on p (by induction r; induction t; exact H),
  left_inv (to_fun !square_equiv_eq) s # !con_inv_cancel_right # H2

Definition rec_on_t [recursor] {a₁₀ : A}
  {P : forall {a₀₂ a₂₂ : A} {b : a₀₂ = a₂₂} {l : a₁₀ = a₀₂} {r : a₁₀ = a₂₂}, square idp b l r -> Type}
  {a₀₂ a₂₂ : A} {b : a₀₂ = a₂₂} {l : a₁₀ = a₀₂} {r : a₁₀ = a₂₂}
  (s : square idp b l r) (H : P ids) : P s.
  let p : l @ b = r . (eq_of_square s)^-1 @ (concat_1p _) in
  have H2 : P (square_of_eq ((p @ (concat_1p _)^-1)^-1)),
  from eq.rec_on p (by induction b; induction l; exact H),
  have H3 : P (square_of_eq ((eq_of_square s)^-1^-1)),
  from eq.rec_on !con_inv_cancel_right H2,
  have H4 : P (square_of_eq (eq_of_square s)),
  from eq.rec_on !inv_inv H3,
  proof
  left_inv (to_fun !square_equiv_eq) s # H4
  qed

Definition rec_on_tb [recursor] {a : A}
  {P : forall {b : A} {l : a = b} {r : a = b}, square idp idp l r -> Type}
  {b : A} {l : a = b} {r : a = b}
  (s : square idp idp l r) (H : P ids) : P s.
  have H2 : P (square_of_eq (eq_of_square s)),
  from eq.rec_on (eq_of_square s : idp @ r = l) (by induction r; exact H),
  left_inv (to_fun !square_equiv_eq) s # H2

Definition rec_on_lr [recursor] {a : A}
  {P : forall {a' : A} {t : a = a'} {b : a = a'}, square t b idp idp -> Type}
  {a' : A} {t : a = a'} {b : a = a'}
  (s : square t b idp idp) (H : P ids) : P s.
  let p : idp @ b = t . (eq_of_square s)^-1 in
  have H2 : P (square_of_eq (eq_of_square s)^-1^-1),
  from @eq.rec_on _ _ (fun x q => P (square_of_eq q^-1)) _ p (by induction b; exact H),
  to_left_inv (!square_equiv_eq) s # !inv_inv # H2

  --we can also do the other recursors (tl, tr, bl, br, tbl, tbr, tlr, blr), but let's postpone this until they are needed

Definition whisker_square [unfold 14 15 16 17] (r₁₀ : p₁₀ = p₁₀') (r₁₂ : p₁₂ = p₁₂')
  (r₀₁ : p₀₁ = p₀₁') (r₂₁ : p₂₁ = p₂₁') (s : square p₁₀ p₁₂ p₀₁ p₂₁)
  : square p₁₀' p₁₂' p₀₁' p₂₁'.
  by induction r₁₀; induction r₁₂; induction r₀₁; induction r₂₁; exact s

  (* squares commute with some operations on 2-paths *)

Definition square_inv2 {p₁ p₂ p₃ p₄ : a = a'}
  {t : p₁ = p₂} {b : p₃ = p₄} {l : p₁ = p₃} {r : p₂ = p₄} (s : square t b l r)
  : square (inverse2 t) (inverse2 b) (inverse2 l) (inverse2 r).
  by induction s;constructor

Definition square_con2 {p₁ p₂ p₃ p₄ : a₁ = a₂} {q₁ q₂ q₃ q₄ : a₂ = a₃}
  {t₁ : p₁ = p₂} {b₁ : p₃ = p₄} {l₁ : p₁ = p₃} {r₁ : p₂ = p₄}
  {t₂ : q₁ = q₂} {b₂ : q₃ = q₄} {l₂ : q₁ = q₃} {r₂ : q₂ = q₄}
  (s₁ : square t₁ b₁ l₁ r₁) (s₂ : square t₂ b₂ l₂ r₂)
  : square (t₁ ◾ t₂) (b₁ ◾ b₂) (l₁ ◾ l₂) (r₁ ◾ r₂).
  by induction s₂;induction s₁;constructor

  open is_trunc
Definition is_set.elims [H : is_set A] : square p₁₀ p₁₂ p₀₁ p₂₁.
  square_of_eq !is_set.elim

Definition is_trunc_square [instance] (n : trunc_index) [H : is_trunc n .+2 A]
  : is_trunc n (square p₁₀ p₁₂ p₀₁ p₂₁).
  is_trunc_equiv_closed_rev n !square_equiv_eq

  (*Definition square_of_con_inv_hsquare {p₁ p₂ p₃ p₄ : a₁ = a₂} *)
  (*   {t : p₁ = p₂} {b : p₃ = p₄} {l : p₁ = p₃} {r : p₂ = p₄} *)
  (*   (s : square (con_inv_eq_idp t) (con_inv_eq_idp b) (l ◾ r⁻²) idp) *)
  (*     : square t b l r . *)
  (* sorry --by induction s *)

  (* Square fillers *)
  (* TODO replace by "more algebraic" fillers? *)

  variables (p₁₀ p₁₂ p₀₁ p₂₁)
Definition square_fill_t : Σ (p : a₀₀ = a₂₀), square p p₁₂ p₀₁ p₂₁.
  by induction p₀₁; induction p₂₁; exact ⟨_, !vrefl⟩

Definition square_fill_b : Σ (p : a₀₂ = a₂₂), square p₁₀ p p₀₁ p₂₁.
  by induction p₀₁; induction p₂₁; exact ⟨_, !vrefl⟩

Definition square_fill_l : Σ (p : a₀₀ = a₀₂), square p₁₀ p₁₂ p p₂₁.
  by induction p₁₀; induction p₁₂; exact ⟨_, !hrefl⟩

Definition square_fill_r : Σ (p : a₂₀ = a₂₂) , square p₁₀ p₁₂ p₀₁ p.
  by induction p₁₀; induction p₁₂; exact ⟨_, !hrefl⟩

  (* Squares having an 'ap' term on one face *)
  --TODO find better names
Definition square_Flr_ap_idp {c : B} {f : A -> B} (p : forall a, f a = c)
  {a b : A} (q : a = b) : square (p a) (p b) (ap f q) idp .
  by induction q; apply vrfl

Definition square_Flr_idp_ap {c : B} {f : A -> B} (p : forall a, c = f a)
  {a b : A} (q : a = b) : square (p a) (p b) idp (ap f q).
  by induction q; apply vrfl

Definition square_ap_idp_Flr {b : B} {f : A -> B} (p : forall a, f a = b)
  {a b : A} (q : a = b) : square (ap f q) idp (p a) (p b).
  by induction q; apply hrfl

  (* Matching eq_hconcat with hconcat etc. *)
  (* TODO maybe rename hconcat_eq and the like? *)
  variable (s₁₁)
Definition ph_eq_pv_h_vp {p : a₀₀ = a₀₂} (r : p = p₀₁) :
  r @ph s₁₁ =  (concat_1p _)^-1 @pv ((hdeg_square r) @h s₁₁) @vp (concat_1p _).
  by cases r; cases s₁₁; esimp

Definition hdeg_h_eq_pv_ph_vp {p : a₀₀ = a₀₂} (r : p = p₀₁) :
  hdeg_square r @h s₁₁ = (concat_1p _) @pv (r @ph s₁₁) @vp (concat_1p _)^-1.
  by cases r; cases s₁₁; esimp

Definition hp_eq_h {p : a₂₀ = a₂₂} (r : p₂₁ = p) :
  s₁₁ @hp r = s₁₁ @h hdeg_square r.
  by cases r; cases s₁₁; esimp

Definition pv_eq_ph_vdeg_v_vh {p : a₀₀ = a₂₀} (r : p = p₁₀) :
  r @pv s₁₁ = (concat_1p _)^-1 @ph ((vdeg_square r) @v s₁₁) @hp (concat_1p _).
  by cases r; cases s₁₁; esimp

Definition vdeg_v_eq_ph_pv_hp {p : a₀₀ = a₂₀} (r : p = p₁₀) :
  vdeg_square r @v s₁₁ = (concat_1p _) @ph (r @pv s₁₁) @hp (concat_1p _)^-1.
  by cases r; cases s₁₁; esimp

Definition vp_eq_v {p : a₀₂ = a₂₂} (r : p₁₂ = p) :
  s₁₁ @vp r = s₁₁ @v vdeg_square r.
  by cases r; cases s₁₁; esimp

Definition natural_square {f g : A -> B} (p : f == g) (q : a = a') :
  square (p a) (p a') (ap f q) (ap g q).
  square_of_pathover (apd p q)

Definition natural_square_tr {f g : A -> B} (p : f == g) (q : a = a') :
  square (ap f q) (ap g q) (p a) (p a').
  transpose (natural_square p q)

Definition natural_square011 {A A' : Type} {B : A -> Type}
  {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b')
  {l r  : forall (a), B a -> A'} (g : forall (a) (b : B a), l b = r b)
  : square (apd011 l p q) (apd011 r p q) (g b) (g b').
Proof.
  induction q, exact hrfl
Defined.

Definition natural_square0111' {A A' : Type} {B : A -> Type} (C : forall (a), B a -> Type)
  {a a' : A} {p : a = a'} {b : B a} {b' : B a'} {q : b =[p] b'}
  {c : C b} {c' : C b'} (s : c =[apd011 C p q] c')
  {l r  : forall (a) {b : B a}, C b -> A'}
  (g : forall (a) {b : B a} (c : C b), l c = r c)
  : square (apd0111 l p q s) (apd0111 r p q s) (g c) (g c').
Proof.
  induction q, esimp at s, induction s using idp_rec_on, exact hrfl
Defined.

  (* this can be generalized a bit, by making the domain and codomain of k different, and also have *)
  (* a function at the RHS of s (similar to m) *)
Definition natural_square0111 {A A' : Type} {B : A -> Type} (C : forall (a), B a -> Type)
  {a a' : A} {p : a = a'} {b : B a} {b' : B a'} {q : b =[p] b'}
  {c : C b} {c' : C b'} (r : c =[apd011 C p q] c')
  {k : A -> A} {l : forall (a), B a -> B (k a)} (m : forall (a) {b : B a}, C b -> C (l b))
  {f  : forall (a) {b : B a}, C b -> A'}
  (s : forall (a) {b : B a} (c : C b), f (m c) = f c)
  : square (apd0111 (fun a b c => f (m c)) p q r) (apd0111 f p q r) (s c) (s c').
Proof.
  induction q, esimp at r, induction r using idp_rec_on, exact hrfl
Defined.

  (* some higher coherence conditions *)


Definition whisker_bl_whisker_tl_eq (p : a = a')
  : whisker_bl p (whisker_tl p ids) = con.right_inv p @ph vrfl.
  by induction p; reflexivity

Definition ap_is_constant_natural_square {g : B -> C} {f : A -> B} (H : forall a, g (f a) = c) (p : a = a') :
  (ap_is_constant H p)^-1 @ph natural_square H p @hp ap_constant p c =
  whisker_bl (H a') (whisker_tl (H a) ids).
Proof. induction p, esimp, rewrite inv_inv, rewrite whisker_bl_whisker_tl_eq end

Definition inv_ph_eq_of_eq_ph {p : a₀₀ = a₀₂} {r : p₀₁ = p} {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁}
  {s₁₁' : square p₁₀ p₁₂ p p₂₁} (t : s₁₁ = r @ph s₁₁') : r^-1 @ph s₁₁ = s₁₁'.
  by induction r; exact t

  (* the following is used for torus.elim_surf *)
Definition whisker_square_aps_eq {f : A -> B}
  {q₁₀ : f a₀₀ = f a₂₀} {q₀₁ : f a₀₀ = f a₀₂} {q₂₁ : f a₂₀ = f a₂₂} {q₁₂ : f a₀₂ = f a₂₂}
  {r₁₀ : ap f p₁₀ = q₁₀} {r₀₁ : ap f p₀₁ = q₀₁} {r₂₁ : ap f p₂₁ = q₂₁} {r₁₂ : ap f p₁₂ = q₁₂}
  {s₁₁ : p₁₀ @ p₂₁ = p₀₁ @ p₁₂} {t₁₁ : square q₁₀ q₁₂ q₀₁ q₂₁}
  (u : square (ap02 f s₁₁) (eq_of_square t₁₁)
  (ap_con f p₁₀ p₂₁ @ (r₁₀ ◾ r₂₁)) (ap_con f p₀₁ p₁₂ @ (r₀₁ ◾ r₁₂)))
  : whisker_square r₁₀ r₁₂ r₀₁ r₂₁ (aps f (square_of_eq s₁₁)) = t₁₁.
Proof.
  induction r₁₀, induction r₀₁, induction r₁₂, induction r₂₁,
  induction p₁₂, induction p₁₀, induction p₂₁, esimp at *, induction s₁₁, esimp at *,
  esimp [square_of_eq],
  apply eq_of_fn_eq_fn !square_equiv_eq, esimp,
  exact (eq_bot_of_square u)^-1
Defined.

Definition natural_square_eq {A B : Type} {a a' : A} {f g : A -> B} (p : f == g) (q : a = a')
  : natural_square p q = square_of_pathover (apd p q).
  idp

Definition eq_of_square_hrfl_hconcat_eq {A : Type} {a a' : A} {p p' : a = a'} (q : p = p')
  : eq_of_square (hrfl @hp q^-1) = (concat_1p _) @ q.
  by induction q; induction p; reflexivity

Definition aps_vrfl {A B : Type} {a a' : A} (f : A -> B) (p : a = a') :
  aps f (vrefl p) = vrefl (ap f p).
  by induction p; reflexivity

Definition aps_hrfl {A B : Type} {a a' : A} (f : A -> B) (p : a = a') :
  aps f (hrefl p) = hrefl (ap f p).
  by induction p; reflexivity

  (* should the following two equalities be cubes? *)
Definition natural_square_ap_fn {A B C : Type} {a a' : A} {g h : A -> B} (f : B -> C) (p : g == h)
  (q : a = a') : natural_square (fun a => ap f (p a)) q =
  ap_compose f g q @ph (aps f (natural_square p q) @hp (ap_compose f h q)^-1).
Proof.
  induction q, exact !aps_vrfl^-1
Defined.

Definition natural_square_compose {A B C : Type} {a a' : A} {g g' : B -> C}
  (p : g == g') (f : A -> B) (q : a = a') : natural_square (fun a => p (f a)) q =
  ap_compose g f q @ph (natural_square p (ap f q) @hp (ap_compose g' f q)^-1).
  by induction q; reflexivity

Definition natural_square_eq2 {A B : Type} {a a' : A} {f f' : A -> B} (p : f == f') {q q' : a = a'}
  (r : q = q') : natural_square p q = ap02 f r @ph (natural_square p q' @hp (ap02 f' r)^-1).
  by induction r; reflexivity

Definition natural_square_refl {A B : Type} {a a' : A} (f : A -> B) (q : a = a')
  : natural_square (homotopy.refl f) q = hrfl.
  by induction q; reflexivity

Definition aps_eq_hconcat {p₀₁'} (f : A -> B) (q : p₀₁' = p₀₁) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) :
  aps f (q @ph s₁₁) = ap02 f q @ph aps f s₁₁.
  by induction q; reflexivity

Definition aps_hconcat_eq {p₂₁'} (f : A -> B) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁' = p₂₁) :
  aps f (s₁₁ @hp r^-1) = aps f s₁₁ @hp (ap02 f r)^-1.
  by induction r; reflexivity

Definition aps_hconcat_eq' {p₂₁'} (f : A -> B) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁ = p₂₁') :
  aps f (s₁₁ @hp r) = aps f s₁₁ @hp ap02 f r.
  by induction r; reflexivity

Definition aps_square_of_eq (f : A -> B) (s : p₁₀ @ p₂₁ = p₀₁ @ p₁₂) :
  aps f (square_of_eq s) = square_of_eq ((ap_con f p₁₀ p₂₁)^-1 @ ap02 f s @ ap_con f p₀₁ p₁₂).
  by induction p₁₂; esimp at *; induction s; induction p₂₁; induction p₁₀; reflexivity

Definition aps_eq_hconcat_eq {p₀₁' p₂₁'} (f : A -> B) (q : p₀₁' = p₀₁) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  (r : p₂₁' = p₂₁) : aps f (q @ph s₁₁ @hp r^-1) = ap02 f q @ph aps f s₁₁ @hp (ap02 f r)^-1.
  by induction q; induction r; reflexivity

Defined. eq
