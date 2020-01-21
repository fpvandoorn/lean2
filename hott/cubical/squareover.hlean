(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Squareovers
*)

import .square

open eq equiv is_equiv sigma

namespace eq

  (* we give the argument B explicitly, because Lean would find (fun a => B a) by itself, which *)
  (* makes the type uglier (of course the two terms areDefinitionally equal) *)
  inductive squareover {A : Type} (B : A -> Type) {a₀₀ : A} {b₀₀ : B a₀₀} :
  forall {a₂₀ a₀₂ a₂₂ : A}
  {p₁₀ : a₀₀ = a₂₀} {p₁₂ : a₀₂ = a₂₂} {p₀₁ : a₀₀ = a₀₂} {p₂₁ : a₂₀ = a₂₂}
  (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
  {b₂₀ : B a₂₀} {b₀₂ : B a₀₂} {b₂₂ : B a₂₂}
  (q₁₀ : pathover B b₀₀ p₁₀ b₂₀) (q₁₂ : pathover B b₀₂ p₁₂ b₂₂)
  (q₀₁ : pathover B b₀₀ p₀₁ b₀₂) (q₂₁ : pathover B b₂₀ p₂₁ b₂₂),
  Type.
  idsquareo : squareover B ids idpo idpo idpo idpo


  variables {A A' : Type} {B : A -> Type}
  {a a' a'' a₀₀ a₂₀ a₄₀ a₀₂ a₂₂ a₂₄ a₀₄ a₄₂ a₄₄ : A}
  (*a₀₀*) {p₁₀ : a₀₀ = a₂₀} (*a₂₀*) {p₃₀ : a₂₀ = a₄₀} (*a₄₀*)
  {p₀₁ : a₀₀ = a₀₂} (*s₁₁*) {p₂₁ : a₂₀ = a₂₂} (*s₃₁*) {p₄₁ : a₄₀ = a₄₂}
  (*a₀₂*) {p₁₂ : a₀₂ = a₂₂} (*a₂₂*) {p₃₂ : a₂₂ = a₄₂} (*a₄₂*)
  {p₀₃ : a₀₂ = a₀₄} (*s₁₃*) {p₂₃ : a₂₂ = a₂₄} (*s₃₃*) {p₄₃ : a₄₂ = a₄₄}
  (*a₀₄*) {p₁₄ : a₀₄ = a₂₄} (*a₂₄*) {p₃₄ : a₂₄ = a₄₄} (*a₄₄*)
  {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁} {s₃₁ : square p₃₀ p₃₂ p₂₁ p₄₁}
  {s₁₃ : square p₁₂ p₁₄ p₀₃ p₂₃} {s₃₃ : square p₃₂ p₃₄ p₂₃ p₄₃}

  {b₀₀ : B a₀₀} {b₂₀ : B a₂₀} {b₄₀ : B a₄₀}
  {b₀₂ : B a₀₂} {b₂₂ : B a₂₂} {b₄₂ : B a₄₂}
  {b₀₄ : B a₀₄} {b₂₄ : B a₂₄} {b₄₄ : B a₄₄}
  (*b₀₀*) {q₁₀ : b₀₀ =[p₁₀] b₂₀} (*b₂₀*) {q₃₀ : b₂₀ =[p₃₀] b₄₀} (*b₄₀*)
  {q₀₁ : b₀₀ =[p₀₁] b₀₂} (*t₁₁*) {q₂₁ : b₂₀ =[p₂₁] b₂₂} (*t₃₁*) {q₄₁ : b₄₀ =[p₄₁] b₄₂}
  (*b₀₂*) {q₁₂ : b₀₂ =[p₁₂] b₂₂} (*b₂₂*) {q₃₂ : b₂₂ =[p₃₂] b₄₂} (*b₄₂*)
  {q₀₃ : b₀₂ =[p₀₃] b₀₄} (*t₁₃*) {q₂₃ : b₂₂ =[p₂₃] b₂₄} (*t₃₃*) {q₄₃ : b₄₂ =[p₄₃] b₄₄}
  (*b₀₄*) {q₁₄ : b₀₄ =[p₁₄] b₂₄} (*b₂₄*) {q₃₄ : b₂₄ =[p₃₄] b₄₄} (*b₄₄*)

Definition squareo . @squareover A B a₀₀
Definition idsquareo (b₀₀ : B a₀₀) . @squareover.idsquareo A B a₀₀ b₀₀
Definition idso                    . @squareover.idsquareo A B a₀₀ b₀₀

Definition apds (f : forall a, B a) (s : square p₁₀ p₁₂ p₀₁ p₂₁)
  : squareover B s (apd f p₁₀) (apd f p₁₂) (apd f p₀₁) (apd f p₂₁).
  square.rec_on s idso

Definition vrflo : squareover B vrfl q₁₀ q₁₀ idpo idpo.
  by induction q₁₀; exact idso

Definition hrflo : squareover B hrfl idpo idpo q₁₀ q₁₀.
  by induction q₁₀; exact idso

Definition vdeg_squareover {p₁₀'} {s : p₁₀ = p₁₀'} {q₁₀' : b₀₀ =[p₁₀'] b₂₀}
  (r : change_path s q₁₀ = q₁₀')
  : squareover B (vdeg_square s) q₁₀ q₁₀' idpo idpo.
  by induction s; esimp at *; induction r; exact vrflo

Definition hdeg_squareover {p₀₁'} {s : p₀₁ = p₀₁'} {q₀₁' : b₀₀ =[p₀₁'] b₀₂}
  (r : change_path s q₀₁ = q₀₁')
  : squareover B (hdeg_square s) idpo idpo q₀₁ q₀₁'.
  by induction s; esimp at *; induction r; exact hrflo

Definition hconcato
  (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁) (t₃₁ : squareover B s₃₁ q₃₀ q₃₂ q₂₁ q₄₁)
  : squareover B (hconcat s₁₁ s₃₁) (q₁₀ @o q₃₀) (q₁₂ @o q₃₂) q₀₁ q₄₁.
  by induction t₃₁; exact t₁₁

Definition vconcato
  (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁) (t₁₃ : squareover B s₁₃ q₁₂ q₁₄ q₀₃ q₂₃)
  : squareover B (vconcat s₁₁ s₁₃) q₁₀ q₁₄ (q₀₁ @o q₀₃) (q₂₁ @o q₂₃).
  by induction t₁₃; exact t₁₁

Definition hinverseo (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁)
  : squareover B (hinverse s₁₁) q₁₀^-1ᵒ q₁₂^-1ᵒ q₂₁ q₀₁.
  by induction t₁₁; constructor

Definition vinverseo (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁)
  : squareover B (vinverse s₁₁) q₁₂ q₁₀ q₀₁^-1ᵒ q₂₁^-1ᵒ.
  by induction t₁₁; constructor

Definition eq_vconcato {q : b₀₀ =[p₁₀] b₂₀}
  (r : q = q₁₀) (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁) : squareover B s₁₁ q q₁₂ q₀₁ q₂₁.
  by induction r; exact t₁₁

Definition vconcato_eq {q : b₀₂ =[p₁₂] b₂₂}
  (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁) (r : q₁₂ = q) : squareover B s₁₁ q₁₀ q q₀₁ q₂₁.
  by induction r; exact t₁₁

Definition eq_hconcato {q : b₀₀ =[p₀₁] b₀₂}
  (r : q = q₀₁) (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁) : squareover B s₁₁ q₁₀ q₁₂ q q₂₁.
  by induction r; exact t₁₁

Definition hconcato_eq {q : b₂₀ =[p₂₁] b₂₂}
  (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁) (r : q₂₁ = q) : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q.
  by induction r; exact t₁₁

Definition pathover_vconcato {p : a₀₀ = a₂₀} {sp : p = p₁₀} {q : b₀₀ =[p] b₂₀}
  (r : change_path sp q = q₁₀) (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁)
  : squareover B (sp @pv s₁₁) q q₁₂ q₀₁ q₂₁.
  by induction sp; induction r; exact t₁₁

Definition vconcato_pathover {p : a₀₂ = a₂₂} {sp : p₁₂ = p} {q : b₀₂ =[p] b₂₂}
  (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁) (r : change_path sp q₁₂ = q)
  : squareover B (s₁₁ @vp sp) q₁₀ q q₀₁ q₂₁.
  by induction sp; induction r; exact t₁₁

Definition pathover_hconcato {p : a₀₀ = a₀₂} {sp : p = p₀₁} {q : b₀₀ =[p] b₀₂}
  (r : change_path sp q = q₀₁) (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁) :
  squareover B (sp @ph s₁₁) q₁₀ q₁₂ q q₂₁.
  by induction sp; induction r; exact t₁₁

Definition hconcato_pathover {p : a₂₀ = a₂₂} {sp : p₂₁ = p} {q : b₂₀ =[p] b₂₂}
  (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁) (r : change_path sp q₂₁ = q) :
  squareover B (s₁₁ @hp sp) q₁₀ q₁₂ q₀₁ q.
  by induction sp; induction r; exact t₁₁

  infix ` @ho `:69 . hconcato --type using \tr
  infix ` @vo `:70 . vconcato --type using \tr
  infix ` @hop `:72 . hconcato_eq --type using \tr
  infix ` @vop `:74 . vconcato_eq --type using \tr
  infix ` @pho `:71 . eq_hconcato --type using \tr
  infix ` @pvo `:73 . eq_vconcato --type using \tr

  (* relating squareovers to squares *)
Definition square_of_squareover (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁) :
  square (!con_tr @ ap (fun a => p₂₁ # a) (tr_eq_of_pathover q₁₀))
  (tr_eq_of_pathover q₁₂)
  (ap (fun q => q # b₀₀) (eq_of_square s₁₁) @ !con_tr @ ap (fun a => p₁₂ # a) (tr_eq_of_pathover q₀₁))
  (tr_eq_of_pathover q₂₁).
  by induction t₁₁; esimp; constructor
(*
Definition squareover_of_square
  (q : square (!con_tr @ ap (fun a => p₂₁ # a) (tr_eq_of_pathover q₁₀))
  (tr_eq_of_pathover q₁₂)
  (ap (fun q => q # b₀₀) (eq_of_square s₁₁) @ !con_tr @ ap (fun a => p₁₂ # a) (tr_eq_of_pathover q₀₁))
  (tr_eq_of_pathover q₂₁))
  : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁.
  sorry
*)

Definition square_of_squareover_ids {b₀₀ b₀₂ b₂₀ b₂₂ : B a}
  {t : b₀₀ = b₂₀} {b : b₀₂ = b₂₂} {l : b₀₀ = b₀₂} {r : b₂₀ = b₂₂}
  (so : squareover B ids (pathover_idp_of_eq t)
  (pathover_idp_of_eq b)
  (pathover_idp_of_eq l)
  (pathover_idp_of_eq r)) : square t b l r.
Proof.
  note H . square_of_squareover so,  (* use apply ... in *)
  rewrite [▸* at H,+idp_con at H,+ap_id at H,↑pathover_idp_of_eq at H],
  rewrite [+to_right_inv !(pathover_equiv_tr_eq (refl a)) at H],
  exact H
Defined.

Definition squareover_ids_of_square {b₀₀ b₀₂ b₂₀ b₂₂ : B a}
  {t : b₀₀ = b₂₀} {b : b₀₂ = b₂₂} {l : b₀₀ = b₀₂} {r : b₂₀ = b₂₂} (q : square t b l r)
  : squareover B ids (pathover_idp_of_eq t)
  (pathover_idp_of_eq b)
  (pathover_idp_of_eq l)
  (pathover_idp_of_eq r).
  square.rec_on q idso

  (* relating pathovers to squareovers *)
Definition pathover_of_squareover' (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁)
  : q₁₀ @o q₂₁ =[eq_of_square s₁₁] q₀₁ @o q₁₂.
  by induction t₁₁; constructor

Definition pathover_of_squareover {s : p₁₀ @ p₂₁ = p₀₁ @ p₁₂}
  (t₁₁ : squareover B (square_of_eq s) q₁₀ q₁₂ q₀₁ q₂₁)
  : q₁₀ @o q₂₁ =[s] q₀₁ @o q₁₂.
Proof.
  revert s t₁₁, refine equiv_rect' !square_equiv_eq^-1ᵉ (fun a b => squareover B b _ _ _ _ -> _) _,
  intro s, exact pathover_of_squareover'
Defined.

Definition squareover_of_pathover {s : p₁₀ @ p₂₁ = p₀₁ @ p₁₂}
  (r : q₁₀ @o q₂₁ =[s] q₀₁ @o q₁₂) : squareover B (square_of_eq s) q₁₀ q₁₂ q₀₁ q₂₁.
  by induction q₁₂; esimp [concato] at r;induction r;induction q₂₁;induction q₁₀;constructor

Definition pathover_top_of_squareover (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁)
  : q₁₀ =[eq_top_of_square s₁₁] q₀₁ @o q₁₂ @o q₂₁^-1ᵒ.
  by induction t₁₁; constructor

Definition squareover_of_pathover_top {s : p₁₀ = p₀₁ @ p₁₂ @ p₂₁^-1}
  (r : q₁₀ =[s] q₀₁ @o q₁₂ @o q₂₁^-1ᵒ)
  : squareover B (square_of_eq_top s) q₁₀ q₁₂ q₀₁ q₂₁.
  by induction q₂₁; induction q₁₂; esimp at r;induction r;induction q₁₀;constructor

Definition pathover_of_hdeg_squareover {p₀₁' : a₀₀ = a₀₂} {r : p₀₁ = p₀₁'} {q₀₁' : b₀₀ =[p₀₁'] b₀₂}
  (t : squareover B (hdeg_square r) idpo idpo q₀₁ q₀₁') : q₀₁ =[r] q₀₁'.
  by induction r; induction q₀₁'; exact (pathover_of_squareover' t)^-1ᵒ

Definition pathover_of_vdeg_squareover {p₁₀' : a₀₀ = a₂₀} {r : p₁₀ = p₁₀'} {q₁₀' : b₀₀ =[p₁₀'] b₂₀}
  (t : squareover B (vdeg_square r) q₁₀ q₁₀' idpo idpo) : q₁₀ =[r] q₁₀'.
  by induction r; induction q₁₀'; exact pathover_of_squareover' t

Definition squareover_of_eq_top (r : change_path (eq_top_of_square s₁₁) q₁₀ = q₀₁ @o q₁₂ @o q₂₁^-1ᵒ)
  : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁.
Proof.
  induction s₁₁, revert q₁₂ q₁₀ r,
  eapply idp_rec_on q₂₁, clear q₂₁,
  intro q₁₂,
  eapply idp_rec_on q₁₂, clear q₁₂,
  esimp, intros,
  induction r, eapply idp_rec_on q₁₀,
  constructor
Defined.

Definition eq_top_of_squareover (r : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁)
  : change_path (eq_top_of_square s₁₁) q₁₀ = q₀₁ @o q₁₂ @o q₂₁^-1ᵒ.
  by induction r; reflexivity

Definition change_square {s₁₁'} (p : s₁₁ = s₁₁') (r : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁)
  : squareover B s₁₁' q₁₀ q₁₂ q₀₁ q₂₁.
  p # r

  (*
Definition squareover_equiv_pathover (q₁₀ : b₀₀ =[p₁₀] b₂₀) (q₁₂ : b₀₂ =[p₁₂] b₂₂)
  (q₀₁ : b₀₀ =[p₀₁] b₀₂) (q₂₁ : b₂₀ =[p₂₁] b₂₂)
  : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁ <~> q₁₀ @o q₂₁ =[eq_of_square s₁₁] q₀₁ @o q₁₂.
Proof.
  fapply equiv.MK,
  { exact pathover_of_squareover},
  { intro r, rewrite [-to_left_inv !square_equiv_eq s₁₁], apply squareover_of_pathover, exact r},
  { intro r, }, --need characterization of squareover lying over ids.
  { intro s, induction s, apply idp},
Defined.
  *)

Definition eq_of_vdeg_squareover {q₁₀' : b₀₀ =[p₁₀] b₂₀}
  (p : squareover B vrfl q₁₀ q₁₀' idpo idpo) : q₁₀ = q₁₀'.
Proof.
  note H . square_of_squareover p,  (* use apply ... in *)
  induction p₁₀, (* if needed we can remove this induction and use con_tr_idp in types/eq2 *)
  rewrite [▸* at H,idp_con at H,+ap_id at H],
  let H' . eq_of_vdeg_square H,
  exact eq_of_fn_eq_fn !pathover_equiv_tr_eq H'
Defined.

  (*Definition vdeg_tr_squareover {q₁₂ : p₀₁ # b₀₀ =[p₁₂] p₂₁ # b₂₀} (r : q₁₀ =[_] q₁₂) *)
  (*   : squareover B s₁₁ q₁₀ q₁₂ !pathover_tr !pathover_tr . *)
  (* by induction p;exact vrflo *)

  (* A version of eq_pathover where the type of the equality also varies *)
Definition eq_pathover_dep {f g : forall a, B a} {p : a = a'} {q : f a = g a}
  {r : f a' = g a'} (s : squareover B hrfl (pathover_idp_of_eq q) (pathover_idp_of_eq r)
  (apd f p) (apd g p)) : q =[p] r.
Proof.
  induction p, apply pathover_idp_of_eq, apply eq_of_vdeg_square, exact square_of_squareover_ids s
Defined.

  (* charcaterization of pathovers in pathovers *)
  (* in this version the fibration (B) of the pathover does not depend on the variable (a) *)
Definition pathover_pathover {a' a₂' : A'} {p : a' = a₂'} {f g : A' -> A}
  {b : forall a, B (f a)} {b₂ : forall a, B (g a)} {q : forall (a' : A'), f a' = g a'}
  (r : pathover B (b a') (q a') (b₂ a'))
  (r₂ : pathover B (b a₂') (q a₂') (b₂ a₂'))
  (s : squareover B (natural_square q p) r r₂
  (pathover_ap B f (apd b p)) (pathover_ap B g (apd b₂ p)))
  : pathover (fun a => pathover B (b a) (q a) (b₂ a)) r p r₂.
Proof.
  induction p, esimp at s, apply pathover_idp_of_eq, apply eq_of_vdeg_squareover, exact s
Defined.

Definition squareover_change_path_left {p₀₁' : a₀₀ = a₀₂} (r : p₀₁' = p₀₁)
  {q₀₁ : b₀₀ =[p₀₁'] b₀₂} (t : squareover B (r @ph s₁₁) q₁₀ q₁₂ q₀₁ q₂₁)
  : squareover B s₁₁ q₁₀ q₁₂ (change_path r q₀₁) q₂₁.
  by induction r; exact t

Definition squareover_change_path_right {p₂₁' : a₂₀ = a₂₂} (r : p₂₁' = p₂₁)
  {q₂₁ : b₂₀ =[p₂₁'] b₂₂} (t : squareover B (s₁₁ @hp r^-1) q₁₀ q₁₂ q₀₁ q₂₁)
  : squareover B s₁₁ q₁₀ q₁₂ q₀₁ (change_path r q₂₁).
  by induction r; exact t

Definition squareover_change_path_right' {p₂₁' : a₂₀ = a₂₂} (r : p₂₁ = p₂₁')
  {q₂₁ : b₂₀ =[p₂₁'] b₂₂} (t : squareover B (s₁₁ @hp r) q₁₀ q₁₂ q₀₁ q₂₁)
  : squareover B s₁₁ q₁₀ q₁₂ q₀₁ (change_path r^-1 q₂₁).
  by induction r; exact t

  (* You can construct a square in a sigma-type by giving a squareover *)
Definition square_dpair_eq_dpair {a₀₀ a₂₀ a₀₂ a₂₂ : A}
  {p₁₀ : a₀₀ = a₂₀} {p₀₁ : a₀₀ = a₀₂} {p₂₁ : a₂₀ = a₂₂} {p₁₂ : a₀₂ = a₂₂}
  (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) {b₀₀ : B a₀₀} {b₂₀ : B a₂₀} {b₀₂ : B a₀₂} {b₂₂ : B a₂₂}
  {q₁₀ : b₀₀ =[p₁₀] b₂₀} {q₀₁ : b₀₀ =[p₀₁] b₀₂} {q₂₁ : b₂₀ =[p₂₁] b₂₂} {q₁₂ : b₀₂ =[p₁₂] b₂₂}
  (t₁₁ : squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁) :
  square (dpair_eq_dpair p₁₀ q₁₀) (dpair_eq_dpair p₁₂ q₁₂)
  (dpair_eq_dpair p₀₁ q₀₁) (dpair_eq_dpair p₂₁ q₂₁).
  by induction t₁₁; constructor

Definition sigma_square {v₀₀ v₂₀ v₀₂ v₂₂ : Σa, B a}
  {p₁₀ : v₀₀ = v₂₀} {p₀₁ : v₀₀ = v₀₂} {p₂₁ : v₂₀ = v₂₂} {p₁₂ : v₀₂ = v₂₂}
  (s₁₁ : square p₁₀..1 p₁₂..1 p₀₁..1 p₂₁..1)
  (t₁₁ : squareover B s₁₁ p₁₀..2 p₁₂..2 p₀₁..2 p₂₁..2) : square p₁₀ p₁₂ p₀₁ p₂₁.
Proof.
  induction v₀₀, induction v₂₀, induction v₀₂, induction v₂₂,
  rewrite [▸* at *, -sigma_eq_eta p₁₀, -sigma_eq_eta p₁₂, -sigma_eq_eta p₀₁, -sigma_eq_eta p₂₁],
  exact square_dpair_eq_dpair s₁₁ t₁₁
Defined.

Defined. eq
