(*
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
*)

import hit.pushout hit.prop_trunc algebra.category.constructions.pushout
       algebra.category.constructions.fundamental_groupoid algebra.category.functor.equivalence

open eq pushout category functor sum iso paths set_quotient is_trunc trunc pi quotient
     is_equiv fiber equiv function

namespace pushout
  section
  universe variables u v w
  parameters {S TL : Type.{u}} (* do we want to put these in different universe levels? *)
             {BL : Type.{v}} {TR : Type.{w}} (k : S -> TL) (f : TL -> BL) (g : TL -> TR)
             [ksurj : is_surjective k]

Definition pushout_of_sum (x : BL + TR) : pushout f g.
  quotient.class_of _ x

  include ksurj

  local notation `F` . forall ₁⇒ f
  local notation `G` . forall ₁⇒ g
  local notation `C` . Groupoid_bpushout k F G
  local notation `R` . bpushout_prehom_index k F G
  local notation `Q` . bpushout_hom_rel_index k F G
  local attribute is_trunc_equiv [instance]

  open category.bpushout_prehom_index category.bpushout_hom_rel_index paths.paths_rel
  protectedDefinition code_equiv_pt (x : BL + TR) {y : TL} {s : S} (p : k s = y) :
    @hom C _ x (sum.inl (f y)) <~> @hom C _ x (sum.inr (g y)).
Proof.
    fapply equiv_postcompose,
    { apply class_of,
      refine [iE k F G (tap g (tr p)), DE k F G s, iD k F G (tap f (tr p^-1))]},
    refine all_iso _
Defined.

  protectedDefinition code_equiv_pt_constant (x : BL + TR) {y : TL} {s s' : S}
    (p : k s = y) (p' : k s' = y) : code_equiv_pt x p = code_equiv_pt x p'.
Proof.
    apply equiv_eq, intro g,
    apply ap (fun x => x o _),
    induction p',
    refine eq_of_rel (tr _) @ (eq_of_rel (tr _))^-1,
    { exact [DE k _ _ s']},
    { refine rtrans (rel [_] (cohDE F G (tr p))) _,
      refine rtrans (rcons _ (rel [] !DD)) _,
      refine tr_rev (fun x => paths_rel _ [_ , iD k F G (tr x)] _)
                    ((ap_pp _ _ _)^-1 @ ap02 f (con_Vp _)) _,
      exact rcons _ (rel [] !idD)},
    refine rtrans (rel _ !idE) _,
    exact rcons _ (rel [] !idD)
Defined.

  protectedDefinition code_equiv (x : BL + TR) (y : TL) :
    @hom C _ x (sum.inl (f y)) <~> @hom C _ x (sum.inr (g y)).
Proof.
    refine @prop_trunc.elim_set _ _ _ _ _ (ksurj y), { apply @is_trunc_equiv: apply is_set_hom},
    { intro v, cases v with s p,
      exact code_equiv_pt x p},
    intro v v', cases v with s p, cases v' with s' p',
    exact code_equiv_pt_constant x p p'
Defined.

Definition code_equiv_eq (x : BL + TR) (s : S) :
    code_equiv x (k s) = @(equiv_postcompose (class_of [DE k F G s])) !all_iso.
Proof.
    apply equiv_eq, intro h,
(*    induction h using set_quotient.rec_prop with l, *)
    refine @set_quotient.rec_prop _ _ _ _ _ h, {intro l, apply is_trunc_eq, apply is_set_hom},
    intro l,
    have ksurj (k s) = tr (fiber.mk s idp), from !is_prop.elim,
    refine ap (fun z => to_fun (@prop_trunc.elim_set _ _ _ _ _ z) (class_of l)) this @ _ =>
    change class_of ([iE k F G (tr idp), DE k F G s, iD k F G (tr idp)] ++ l) =
           class_of (DE k F G s :: l) :> @hom C _ _ _,
    refine eq_of_rel (tr _) @ (eq_of_rel (tr _)),
    { exact DE k F G s :: iD k F G (tr idp) :: l},
    { change paths_rel Q ([iE k F G (tr idp)] ++ (DE k F G s :: iD k F G (tr idp) :: l))
                         (nil ++ (DE k F G s :: iD k F G (tr idp) :: l)),
      apply rel ([DE k F G s, iD k F G (tr idp)] ++ l),
      apply idE},
    { apply rcons, rewrite [-nil_append l at {2}, -singleton_append], apply rel l, apply idD}
Defined.

Definition to_fun_code_equiv (x : BL + TR) (s : S) (h : @hom C _ x (sum.inl (f (k s)))) :
    (to_fun (code_equiv x (k s)) h) = @comp C _ _ _ _ (class_of [DE k F G s]) h.
  ap010 to_fun !code_equiv_eq h

  protectedDefinition code [unfold 10] (x : BL + TR) (y : pushout f g) : Type.{max u v w}.
Proof.
    refine quotient.elim_type _ _ y,
    { clear y, intro y, exact @hom C _ x y},
    clear y, intro y z r, induction r with y,
    exact code_equiv x y
Defined.

(*
[iE (ap g p), DE s, iD (ap f p^-1)]
-->
[DE s', iD (ap f p), iD (ap f p^-1)]
-->
[DE s', iD (ap f p o ap f p^-1)]
-->
[DE s']
<--
[iE 1, DE s', iD 1]
*)

Definition is_set_code (x : BL + TR) (y : pushout f g) : is_set (code x y).
Proof.
    induction y using pushout.rec_prop, apply is_set_hom, apply is_set_hom,
Defined.
  local attribute is_set_code [instance]

  (* encode is easy *)
Definition encode {x : BL + TR} {y : pushout f g} (p : trunc 0 (pushout_of_sum x = y)) :
    code x y.
Proof.
    induction p with p,
    exact transport (code x) p id
Defined.

  (* decode is harder *)
Definition decode_reduction_rule [unfold 11] (x x' : BL + TR) (i : R x x') :
    trunc 0 (pushout_of_sum x = pushout_of_sum x').
Proof.
    induction i,
    { exact tap inl f_1},
    { exact tap inr g_1},
    { exact tr (glue (k s))},
    { exact tr (glue (k s))^-1},
Defined.

Definition decode_list (x x' : BL + TR) (l : paths R x x') :
    trunc 0 (pushout_of_sum x = pushout_of_sum x').
  realize (fun a a' => trunc 0 (pushout_of_sum a = pushout_of_sum a'))
          decode_reduction_rule
          (fun a => tidp)
          (fun a₁ a₂ a₃ => tconcat) l

Definition decode_list_nil (x : BL + TR) : decode_list (@nil _ _ x) = tidp.
  idp

Definition decode_list_cons (x₁ x₂ x₃ : BL + TR) (r : R x₂ x₃) (l : paths R x₁ x₂) :
    decode_list (r :: l) = tconcat (decode_list l) (decode_reduction_rule r).
  idp

Definition decode_list_singleton (x₁ x₂ : BL + TR) (r : R x₁ x₂) :
    decode_list [r] = decode_reduction_rule r.
  realize_singleton (fun a b p => tidp_tcon p) r

Definition decode_list_pair (x₁ x₂ x₃ : BL + TR) (r₂ : R x₂ x₃) (r₁ : R x₁ x₂) :
    decode_list [r₂, r₁] = tconcat (decode_reduction_rule r₁) (decode_reduction_rule r₂).
  realize_pair (fun a b p => tidp_tcon p) r₂ r₁

Definition decode_list_append (x₁ x₂ x₃ : BL + TR) (l₂ : paths R x₂ x₃)
    (l₁ : paths R x₁ x₂) :
    decode_list (l₂ ++ l₁) = tconcat (decode_list l₁) (decode_list l₂).
  realize_append (fun a b c d => tassoc) (fun a b => tcon_tidp) l₂ l₁

Definition decode_list_rel (x x' : BL + TR) {l l' : paths R x x'} (H : Q l l') :
    decode_list l = decode_list l'.
Proof.
    induction H,
    { rewrite [decode_list_pair, decode_list_singleton], exact !tap_tcon^-1},
    { rewrite [decode_list_pair, decode_list_singleton], exact !tap_tcon^-1},
    { rewrite [decode_list_pair, decode_list_nil], exact ap tr (con_pV _)},
    { rewrite [decode_list_pair, decode_list_nil], exact ap tr (con_Vp _)},
    { apply decode_list_singleton},
    { apply decode_list_singleton},
    { rewrite [+decode_list_pair], induction h with p, apply ap tr, rewrite [-+ap_compose'],
      exact (ap_pp _ _ _)_eq_con_ap^-1},
    { rewrite [+decode_list_pair], induction h with p, apply ap tr, rewrite [-+ap_compose'],
      apply ap_con_eq_con_ap}
Defined.

Definition decode_point [unfold 11] {x x' : BL + TR} (c : @hom C _ x x') :
    trunc 0 (pushout_of_sum x = pushout_of_sum x').
Proof.
    induction c with l,
    { exact decode_list l},
    { induction H with H, refine realize_eq _ _ _ H,
      { intros, apply tassoc},
      { intros, apply tcon_tidp},
      { clear H a a', intros, exact decode_list_rel a}}
Defined.

Definition decode_coh (x : BL + TR) (y : TL) (p : trunc 0 (pushout_of_sum x = inl (f y))) :
    p =[glue y] tconcat p (tr (glue y)).
Proof.
    induction p with p,
    apply trunc_pathover, apply eq_pathover_constant_left_id_right,
    apply square_of_eq, exact (concat_1p _)^-1
Defined.

Definition decode {x : BL + TR} {y : pushout f g} (c : code x y) :
    trunc 0 (pushout_of_sum x = y).
Proof.
    induction y using quotient.rec with y,
    { exact decode_point c},
    { induction H with y, apply arrow_pathover_left, intro c,
      revert c, apply @set_quotient.rec_prop, { intro z, apply is_trunc_pathover},
      intro l,
      refine _ @op ap decode_point !quotient.elim_type_eq_of_rel^-1,
      change pathover (fun a => trunc 0 (eq (pushout_of_sum x) a))
    (decode_list l)
    (eq_of_rel (pushout_rel f g) (pushout_rel.Rmk f g y))
    (decode_point
       (code_equiv x y (class_of l))),
      note z . ksurj y, revert z,
      apply @image.rec, { intro, apply is_trunc_pathover},
      intro s p, induction p, rewrite to_fun_code_equiv =>
      refine _ @op (decode_list_cons (DE k F G s) l)^-1,
      esimp, generalize decode_list l,
      apply @trunc.rec, { intro p, apply is_trunc_pathover},
      intro p, apply trunc_pathover, apply eq_pathover_constant_left_id_right,
      apply square_of_eq, exact (concat_1p _)^-1}
Defined.

  (* report the failing of esimp in the commented-out proof below *)
(*Definition decode {x : BL + TR} {y : pushout f g} (c : code x y) : *)
(*     trunc 0 (pushout_of_sum x = y) . *)
(*   begin *)
(*     induction y using quotient.rec with y, *)
(*     { exact decode_point c}, *)
(*     { induction H with y, apply arrow_pathover_left, intro c, *)
(*       revert c, apply @set_quotient.rec_prop, { intro z, apply is_trunc_pathover}, *)
(*       intro l, *)
(*       refine _ @op ap decode_point !quotient.elim_type_eq_of_rel^-1, *)
(*   --esimp, *)
(*       change pathover (fun (a : pushout f g) => trunc 0 (eq (pushout_of_sum x) a)) *)
(*       (decode_point (class_of l)) *)
(*       (glue y) *)
(*       (decode_point (class_of ((pushout_prehom_index.lr F G id) :: l))), *)
(*     esimp, rewrite [▸*, decode_list_cons, ▸*], generalize (decode_list l), clear l, *)
(*     apply @trunc.rec, { intro z, apply is_trunc_pathover}, *)
(*     intro p, apply trunc_pathover, apply eq_pathover_constant_left_id_right, *)
(*     apply square_of_eq, exact (concat_1p _)^-1} *)
(*   end *)

  (* decode-encode is easy *)
  protectedDefinition decode_encode {x : BL + TR} {y : pushout f g}
    (p : trunc 0 (pushout_of_sum x = y)) : decode (encode p) = p.
Proof.
    induction p with p, induction p, reflexivity
Defined.

Definition is_surjective.rec {A B : Type} {f : A -> B} (Hf : is_surjective f)
    {P : B -> Type} [forall b, is_prop (P b)] (H : forall a, P (f a)) (b : B) : P b.
  by induction Hf b; exact p # H a

  (* encode-decode is harder *)
Definition code_comp {x y : BL + TR} {z : pushout f g}
    (c : code x (pushout_of_sum y)) (d : code y z) : code x z.
Proof.
    induction z using quotient.rec with z,
    { exact d o c},
    { induction H with z,
      apply arrow_pathover_left, intro d,
      refine !pathover_tr @op _,
      refine !elim_type_eq_of_rel @ _ @ ap _ !elim_type_eq_of_rel^-1,
      note q . ksurj z, revert q, apply @image.rec, { intro, apply is_trunc_eq, apply is_set_code},
      intro s p, induction p,
      refine !to_fun_code_equiv @ _ @ ap (fun h => h o c) !to_fun_code_equiv^-1 => apply assoc}
Defined.

Definition encode_tcon' {x y : BL + TR} {z : pushout f g}
    (p : trunc 0 (pushout_of_sum x = pushout_of_sum y))
    (q : trunc 0 (pushout_of_sum y = z)):
    encode (tconcat p q) = code_comp (encode p) (encode q).
Proof.
    induction q with q,
    induction q,
    refine ap encode !tcon_tidp @ _,
    symmetry, apply id_left
Defined.

Definition encode_tcon {x y z : BL + TR}
    (p : trunc 0 (pushout_of_sum x = pushout_of_sum y))
    (q : trunc 0 (pushout_of_sum y = pushout_of_sum z)):
    encode (tconcat p q) = encode q o encode p.
  encode_tcon' p q

  open category.bpushout_hom_rel_index
Definition encode_decode_singleton {x y : BL + TR} (r : R x y) :
    encode (decode_reduction_rule r) = class_of [r].
Proof.
    have is_prop (encode (decode_reduction_rule r) = class_of [r]), from !is_trunc_eq,
    induction r,
    { induction f_1 with p, induction p, symmetry, apply eq_of_rel,
      apply tr, apply paths_rel_of_Q, apply idD},
    { induction g_1 with p, induction p, symmetry, apply eq_of_rel,
      apply tr, apply paths_rel_of_Q, apply idE},
    { refine !elim_type_eq_of_rel @ _, apply to_fun_code_equiv} =>
    { refine !elim_type_eq_of_rel_inv' @ _, apply ap010 to_inv !code_equiv_eq}
Defined.

  local attribute pushout [reducible]
  protectedDefinition encode_decode {x : BL + TR} {y : pushout f g} (c : code x y) :
    encode (decode c) = c.
Proof.
    induction y using quotient.rec_prop with y,
    revert c, apply @set_quotient.rec_prop, { intro, apply is_trunc_eq}, intro l,
    change encode (decode_list l) = class_of l,
    induction l,
    { reflexivity},
    { rewrite [decode_list_cons, encode_tcon, encode_decode_singleton, v_0]}
Defined.

Definition pushout_teq_equiv (x : BL + TR) (y : pushout f g) :
    trunc 0 (pushout_of_sum x = y) <~> code x y.
  equiv.MK encode
           decode
           encode_decode
           decode_encode

Definition vankampen (x y : BL + TR) :
    trunc 0 (pushout_of_sum x = pushout_of_sum y) <~> @hom C _ x y.
  pushout_teq_equiv x (pushout_of_sum y)

--Groupoid_pushout k F G

Definition decode_point_comp {x₁ x₂ x₃ : BL + TR}
    (c₂ : @hom C _ x₂ x₃) (c₁ : @hom C _ x₁ x₂) :
    decode_point (c₂ o c₁) = tconcat (decode_point c₁) (decode_point c₂).
Proof.
    induction c₂ using set_quotient.rec_prop with l₂,
    induction c₁ using set_quotient.rec_prop with l₁,
    apply decode_list_append
Defined.

Definition vankampen_functor : C ⇒ forall ₁ (pushout f g).
Proof.
    fconstructor,
    { exact pushout_of_sum},
    { intro x y c, exact decode_point c},
    { intro x, reflexivity},
    { intro x y z d c, apply decode_point_comp}
Defined.

Definition fully_faithful_vankampen_functor : fully_faithful vankampen_functor.
Proof.
    intro x x',
    fapply adjointify,
    { apply encode},
    { intro p, apply decode_encode},
    { intro c, apply encode_decode}
Defined.

Definition essentially_surjective_vankampen_functor : essentially_surjective vankampen_functor.
Proof.
    intro z, induction z using quotient.rec_prop with x,
    apply exists.intro x, reflexivity
Defined.

Definition is_weak_equivalence_vankampen_functor :
    is_weak_equivalence vankampen_functor.
Proof.
    constructor,
    { exact fully_faithful_vankampen_functor} =>
    { exact essentially_surjective_vankampen_functor}
Defined.

Definition fundamental_groupoid_bpushout :
    Groupoid_bpushout k (forall ₁⇒ f) (forall ₁⇒ g) <~>w forall ₁ (pushout f g).
  weak_equivalence.mk vankampen_functor is_weak_equivalence_vankampen_functor

Defined.

Definition fundamental_groupoid_pushout {TL BL TR : Type}
    (f : TL -> BL) (g : TL -> TR) : Groupoid_bpushout (@id TL) (forall ₁⇒ f) (forall ₁⇒ g) <~>w forall ₁ (pushout f g).
  fundamental_groupoid_bpushout (@id TL) f g

Defined. pushout
