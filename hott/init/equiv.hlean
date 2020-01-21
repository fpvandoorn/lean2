(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
*)

prelude
import .path .function
open eq function lift

(* Equivalences *)

(* This is ourDefinition of equivalence. In the HoTT-book it's called *)
(* ihae (half-adjoint equivalence). *)
structure is_equiv [class] {A B : Type} (f : A -> B).
mk' ::
  (inv : B -> A)
  (right_inv : forall b, f (inv b) = b)
  (left_inv : forall a, inv (f a) = a)
  (adj : forall x, right_inv (f x) = ap f (left_inv x))



(* A more bundled version of equivalence *)
structure equiv (A B : Type).
  (to_fun : A -> B)
  (to_is_equiv : is_equiv to_fun)

namespace is_equiv
  (* Some instances and closure properties of equivalences *)
  postfix ^-1 . inv
  (* a second notation for the inverse, which is not overloaded *)
  postfix [parsing_only] `^-1ᶠ`:std.prec.max_plus . inv

  section
  variables {A B C : Type} (g : B -> C) (f : A -> B) {f' : A -> B}

  (* The variant of mk' where f is explicit. *)
  protectedDefinition mk . @is_equiv.mk' A B f

  (* The identity function is an equivalence. *)
Definition is_equiv_id [instance] (A : Type) : (is_equiv (id : A -> A)).
  is_equiv.mk id id (fun a => idp) (fun a => idp) (fun a => idp)

  (* The composition of two equivalences is, again, an equivalence. *)
Definition is_equiv_compose [Hf : is_equiv f] [Hg : is_equiv g]
    : is_equiv (g o f).
  is_equiv.mk (g o f) (f^-1 o g^-1)
             abstract (fun c => ap g (right_inv f (g^-1 c)) @ right_inv g c) end
             abstract (fun a => ap (inv f) (left_inv g (f a)) @ left_inv f a) end
             abstract (fun a => (whisker_left _ (adj g (f a))) @
                  (ap_con g _ _)^-1 @
                  ap02 g ((ap_con_eq_con (right_inv f) (left_inv g (f a)))^-1 @
                          (ap_compose f (inv f) _ ◾  adj f a) @
                          (ap_con f _ _)^-1
                         ) @
                  (ap_compose g f _)^-1) end

  (* Any function equal to an equivalence is an equivlance as well. *)
  variable {f}
Definition is_equiv_eq_closed [Hf : is_equiv f] (Heq : f = f') : is_equiv f'.
  eq.rec_on Heq Hf
Defined.

  section
  parameters {A B : Type} (f : A -> B) (g : B -> A)
            (ret : forall b, f (g b) = b) (sec : forall a, g (f a) = a)

Definition adjointify_left_inv' [unfold_full] (a : A) : g (f a) = a.
  ap g (ap f (inverse (sec a))) @ ap g (ret (f a)) @ sec a

Definition adjointify_adj' (a : A) : ret (f a) = ap f (adjointify_left_inv' a).
  let fgretrfa . ap f (ap g (ret (f a))) in
  let fgfinvsect . ap f (ap g (ap f (sec a)^-1)) in
  let fgfa . f (g (f a)) in
  let retrfa . ret (f a) in
  have eq1 : ap f (sec a) = _,
    from calc ap f (sec a)
          = idp @ ap f (sec a)                                     : by rewrite idp_con
      ... = (ret (f a) @ (ret (f a))^-1) @ ap f (sec a)             : by rewrite con.right_inv
      ... = ((ret fgfa)^-1 @ ap (f o g) (ret (f a))) @ ap f (sec a) : by rewrite con_ap_eq_con
      ... = ((ret fgfa)^-1 @ fgretrfa) @ ap f (sec a)               : by rewrite ap_compose
      ... = (ret fgfa)^-1 @ (fgretrfa @ ap f (sec a))               : by rewrite con.assoc,
  have eq2 : ap f (sec a) @ idp = (ret fgfa)^-1 @ (fgretrfa @ ap f (sec a)),
    from (concat_p1 _) @ eq1,
  have eq3 : idp = _,
    from calc idp
          = (ap f (sec a))^-1 @ ((ret fgfa)^-1 @ (fgretrfa @ ap f (sec a))) : eq_inv_con_of_con_eq eq2
      ... = ((ap f (sec a))^-1 @ (ret fgfa)^-1) @ (fgretrfa @ ap f (sec a)) : by rewrite con.assoc'
      ... = (ap f (sec a)^-1 @ (ret fgfa)^-1) @ (fgretrfa @ ap f (sec a))   : by rewrite ap_inv
      ... = ((ap f (sec a)^-1 @ (ret fgfa)^-1) @ fgretrfa) @ ap f (sec a)   : by rewrite con.assoc'
      ... = ((retrfa^-1 @ ap (f o g) (ap f (sec a)^-1)) @ fgretrfa) @ ap f (sec a) : by rewrite con_ap_eq_con
 ... = ((retrfa^-1 @ fgfinvsect) @ fgretrfa) @ ap f (sec a)           : by rewrite ap_compose
      ... = (retrfa^-1 @ (fgfinvsect @ fgretrfa)) @ ap f (sec a)           : by rewrite con.assoc'
      ... = retrfa^-1 @ ap f (ap g (ap f (sec a)^-1) @ ap g (ret (f a))) @ ap f (sec a)   : by rewrite ap_con
      ... = retrfa^-1 @ (ap f (ap g (ap f (sec a)^-1) @ ap g (ret (f a))) @ ap f (sec a)) : by rewrite con.assoc'
      ... = retrfa^-1 @ ap f ((ap g (ap f (sec a)^-1) @ ap g (ret (f a))) @ sec a)        : by rewrite -ap_con,
  show ret (f a) = ap f ((ap g (ap f (sec a)^-1) @ ap g (ret (f a))) @ sec a),
    from eq_of_idp_eq_inv_con eq3

Definition adjointify : is_equiv f.
  is_equiv.mk f g ret adjointify_left_inv' adjointify_adj'
Defined.

  (* Any function pointwise equal to an equivalence is an equivalence as well. *)
Definition homotopy_closed {A B : Type} (f : A -> B) {f' : A -> B} [Hf : is_equiv f]
    (Hty : f == f') : is_equiv f'.
  adjointify f'
             (inv f)
             (fun b => (Hty (inv f b))^-1 @ right_inv f b)
             (fun a => (ap (inv f) (Hty a))^-1 @ left_inv f a)

Definition inv_homotopy_closed {A B : Type} {f : A -> B} {f' : B -> A}
    [Hf : is_equiv f] (Hty : f^-1 == f') : is_equiv f.
  adjointify f
             f'
             (fun b => ap f !Hty^-1 @ right_inv f b)
             (fun a => !Hty^-1 @ left_inv f a)

Definition inv_homotopy_inv {A B : Type} {f g : A -> B} [is_equiv f] [is_equiv g] (p : f == g)
    : f^-1 == g^-1.
  fun b => (left_inv g (f^-1 b))^-1 @ ap g^-1 ((p (f^-1 b))^-1 @ right_inv f b)

Definition is_equiv_up [instance] (A : Type)
    : is_equiv (up : A -> lift A).
  adjointify up down (fun a => by induction a;reflexivity) (fun a => idp)

  section
  variables {A B C : Type} (f : A -> B) {f' : A -> B} [Hf : is_equiv f] (g : B -> C)
  include Hf

  (* The function equiv_rect says that given an equivalence f : A -> B => *)
  (* and a hypothesis from B, one may always assume that the hypothesis *)
  (* is in the image of e. *)

  (* In fibrational terms, if we have a fibration over B which has a section *)
  (* once pulled back along an equivalence f : A -> B, then it has a section *)
  (* over all of B. *)

Definition is_equiv_rect (P : B -> Type) (g : forall a, P (f a)) (b : B) : P b.
  right_inv f b # g (f^-1 b)

Definition is_equiv_rect' (P : A -> B -> Type) (g : forall b, P (f^-1 b) b) (a : A) : P a (f a).
  left_inv f a # g (f a)

Definition is_equiv_rect_comp (P : B -> Type)
      (df : forall (x : A), P (f x)) (x : A) : is_equiv_rect f P df (f x) = df x.
  calc
    is_equiv_rect f P df (f x)
          = right_inv f (f x) # df (f^-1 (f x))   : by esimp
      ... = ap f (left_inv f x) # df (f^-1 (f x)) : by rewrite -adj
      ... = left_inv f x # df (f^-1 (f x))        : by rewrite -tr_compose
      ... = df x                                 : by rewrite (apdt df (left_inv f x))

Definition adj_inv (b : B) : left_inv f (f^-1 b) = ap f^-1 (right_inv f b).
  is_equiv_rect f _
    (fun a => eq.cancel_right (left_inv f (id a))
           (whisker_left _ !ap_id^-1 @ (ap_con_eq_con_ap (left_inv f) (left_inv f a))^-1) @
      !ap_compose @ ap02 f^-1 (adj f a)^-1)
    b

  --The inverse of an equivalence is, again, an equivalence.
Definition is_equiv_inv [instance] [priority 500] : is_equiv f^-1.
  is_equiv.mk f^-1 f (left_inv f) (right_inv f) (adj_inv f)

  (* The 2-out-of-3 properties *)
Definition cancel_right (g : B -> C) [Hgf : is_equiv (g o f)] : (is_equiv g).
  have Hfinv : is_equiv f^-1, from is_equiv_inv f,
  @homotopy_closed _ _ _ _ (is_equiv_compose (g o f) f^-1) (fun b => ap g (@right_inv _ _ f _ b))

Definition cancel_left (g : C -> A) [Hgf : is_equiv (f o g)] : (is_equiv g).
  have Hfinv : is_equiv f^-1, from is_equiv_inv f,
  @homotopy_closed _ _ _ _ (is_equiv_compose f^-1 (f o g)) (fun a => left_inv f (g a))

Definition eq_of_fn_eq_fn' {x y : A} (q : f x = f y) : x = y.
  (left_inv f x)^-1 @ ap f^-1 q @ left_inv f y

Definition ap_eq_of_fn_eq_fn' {x y : A} (q : f x = f y) : ap f (eq_of_fn_eq_fn' f q) = q.
  (ap_pp _ _ _) @ whisker_right _ (ap_pp _ _ _)
          @ ((!ap_inv @ inverse2 (adj f _)^-1)
            ◾ (inverse (ap_compose f f^-1 _))
            ◾ (adj f _)^-1)
          @ con_ap_con_eq_con_con (right_inv f) _ _
          @ whisker_right _ (con_Vp _)
          @ (concat_1p _)

Definition eq_of_fn_eq_fn'_ap {x y : A} (q : x = y) : eq_of_fn_eq_fn' f (ap f q) = q.
  by induction q; apply con.left_inv

Definition is_equiv_ap [instance] (x y : A) : is_equiv (ap f : x = y -> f x = f y).
  adjointify
    (ap f)
    (eq_of_fn_eq_fn' f)
    (ap_eq_of_fn_eq_fn' f)
    (eq_of_fn_eq_fn'_ap f)

Defined.

  section
  variables {A B C : Type} {f : A -> B} [Hf : is_equiv f]
  include Hf

  section rewrite_rules
    variables {a : A} {b : B}
Definition eq_of_eq_inv (p : a = f^-1 b) : f a = b.
    ap f p @ right_inv f b

Definition eq_of_inv_eq (p : f^-1 b = a) : b = f a.
    (eq_of_eq_inv p^-1)^-1

Definition inv_eq_of_eq (p : b = f a) : f^-1 b = a.
    ap f^-1 p @ left_inv f a

Definition eq_inv_of_eq (p : f a = b) : a = f^-1 b.
    (inv_eq_of_eq p^-1)^-1
Defined. rewrite_rules

  variable (f)

  section pre_compose
    variables (α : A -> C) (β : B -> C)

Definition homotopy_of_homotopy_inv_pre (p : β == α o f^-1) : β o f == α.
    fun a => p (f a) @ ap α (left_inv f a)

Definition homotopy_of_inv_homotopy_pre (p : α o f^-1 == β) : α == β o f.
    fun a => (ap α (left_inv f a))^-1 @ p (f a)

Definition inv_homotopy_of_homotopy_pre (p : α == β o f) : α o f^-1 == β.
    fun b => p (f^-1 b) @ ap β (right_inv f b)

Definition homotopy_inv_of_homotopy_pre (p : β o f == α) : β == α o f^-1 .
    fun b => (ap β (right_inv f b))^-1 @ p (f^-1 b)
Defined. pre_compose

  section post_compose
    variables (α : C -> A) (β : C -> B)

Definition homotopy_of_homotopy_inv_post (p : α == f^-1 o β) : f o α == β.
    fun c => ap f (p c) @ (right_inv f (β c))

Definition homotopy_of_inv_homotopy_post (p : f^-1 o β == α) : β == f o α.
    fun c => (right_inv f (β c))^-1 @ ap f (p c)

Definition inv_homotopy_of_homotopy_post (p : β == f o α) : f^-1 o β == α.
    fun c => ap f^-1 (p c) @ (left_inv f (α c))

Definition homotopy_inv_of_homotopy_post (p : f o α == β) : α == f^-1 o β.
    fun c => (left_inv f (α c))^-1 @ ap f^-1 (p c)
Defined. post_compose

Defined.

  --Transporting is an equivalence
Definition is_equiv_tr {A : Type} (P : A -> Type) {x y : A}
    (p : x = y) : (is_equiv (transport P p)).
  is_equiv.mk _ (transport P p^-1) (tr_inv_tr p) (inv_tr_tr p) (tr_inv_tr_lemma p)

  (* a version where the transport is a cast. Note: A and B live in the same universe here. *)
Definition is_equiv_cast {A B : Type} (H : A = B) : is_equiv (cast H).
  is_equiv_tr (fun X => X) H

  section
  variables {A : Type} {B C : A -> Type} (f : forall {a}, B a -> C a) [H : forall a, is_equiv (@f a)]
            {g : A -> A} {g' : A -> A} (h : forall {a}, B (g' a) -> B (g a)) (h' : forall {a}, C (g' a) -> C (g a))

  include H
Definition inv_commute' (p : forall (a : A) (b : B (g' a)), f (h b) = h' (f b)) {a : A}
    (c : C (g' a)) : f^-1 (h' c) = h (f^-1 c).
  eq_of_fn_eq_fn' f (right_inv f (h' c) @ ap h' (right_inv f c)^-1 @ (p (f^-1 c))^-1)

Definition fun_commute_of_inv_commute' (p : forall , f^-1 (h' c) = h (f^-1 c))
    {a : A} (b : B (g' a)) : f (h b) = h' (f b).
  eq_of_fn_eq_fn' f^-1 (left_inv f (h b) @ ap h (left_inv f b)^-1 @ (p (f b))^-1)

Definition ap_inv_commute' (p : forall (a : A) (b : B (g' a)), f (h b) = h' (f b)) {a : A}
    (c : C (g' a)) : ap f (inv_commute' @f @h @h' p c)
                       = right_inv f (h' c) @ ap h' (right_inv f c)^-1 @ (p (f^-1 c))^-1.
  !ap_eq_of_fn_eq_fn'

  (* inv_commute'_fn is in types.equiv *)
Defined.

  (* This is inv_commute' for A ≡ unit *)
Definition inv_commute1' {B C : Type} (f : B -> C) [is_equiv f] (h : B -> B) (h' : C -> C)
    (p : forall (b : B), f (h b) = h' (f b)) (c : C) : f^-1 (h' c) = h (f^-1 c).
  eq_of_fn_eq_fn' f (right_inv f (h' c) @ ap h' (right_inv f c)^-1 @ (p (f^-1 c))^-1)

Defined. is_equiv
open is_equiv

namespace eq
  local attribute is_equiv_tr [instance]

Definition tr_inv_fn {A : Type} {B : A -> Type} {a a' : A} (p : a = a') :
    transport B p^-1 = (transport B p)^-1 . idp
Definition tr_inv {A : Type} {B : A -> Type} {a a' : A} (p : a = a') (b : B a') :
    p^-1 # b = (transport B p)^-1 b . idp

Definition cast_inv_fn {A B : Type} (p : A = B) : cast p^-1 = (cast p)^-1 . idp
Definition cast_inv {A B : Type} (p : A = B) (b : B) : cast p^-1 b = (cast p)^-1 b . idp
Defined. eq

infix ` <~> `:25 . equiv


namespace equiv
  attribute to_fun [coercion]

  section
  variables {A B C : Type}

  protectedDefinition MK (f : A -> B) (g : B -> A)
    (right_inv : forall b, f (g b) = b) (left_inv : forall a, g (f a) = a) : A <~> B.
  equiv.mk f (adjointify f g right_inv left_inv)

Definition to_inv (f : A <~> B) : B -> A . f^-1
Definition to_right_inv (f : A <~> B) (b : B) : f (f^-1 b) = b.
  right_inv f b
Definition to_left_inv (f : A <~> B) (a : A) : f^-1 (f a) = a.
  left_inv f a

  protectedDefinition rfl [refl] : A <~> A.
  equiv.mk id !is_equiv_id

  protectedDefinition refl (A : Type) : A <~> A.
  @equiv.rfl A

  protectedDefinition symm [symm] (f : A <~> B) : B <~> A.
  equiv.mk f^-1 !is_equiv_inv

  protectedDefinition trans [trans] (f : A <~> B) (g : B <~> C) : A <~> C.
  equiv.mk (g o f) !is_equiv_compose

  infixl ` @e `:75 . equiv.trans
  postfix `^-1ᵉ`:(max + 1) . equiv.symm
    (* notation for inverse which is not overloaded *)
  abbreviation erfl . @equiv.rfl

Definition to_inv_trans [unfold_full] (f : A <~> B) (g : B <~> C)
    : to_inv (f @e g) = to_fun (g^-1ᵉ @e f^-1ᵉ).
  idp

Definition equiv_change_fun (f : A <~> B) {f' : A -> B} (Heq : f == f') : A <~> B.
  equiv.mk f' (is_equiv.homotopy_closed f Heq)

Definition equiv_change_inv (f : A <~> B) {f' : B -> A} (Heq : f^-1 == f')
    : A <~> B.
  equiv.mk f (inv_homotopy_closed Heq)

  --rename: eq_equiv_fn_eq_fn_of_is_equiv
Definition eq_equiv_fn_eq (f : A -> B) [H : is_equiv f] (a b : A) : (a = b) <~> (f a = f b).
  equiv.mk (ap f) !is_equiv_ap

  --rename: eq_equiv_fn_eq_fn
Definition eq_equiv_fn_eq_of_equiv (f : A <~> B) (a b : A) : (a = b) <~> (f a = f b).
  equiv.mk (ap f) !is_equiv_ap

Definition equiv_ap (P : A -> Type) {a b : A} (p : a = b) : P a <~> P b.
  equiv.mk (transport P p) !is_equiv_tr

Definition equiv_of_eq {A B : Type} (p : A = B) : A <~> B.
  equiv.mk (cast p) !is_equiv_tr

Definition equiv_of_eq_refl [unfold_full] (A : Type)
    : equiv_of_eq (refl A) = equiv.refl A.
  idp

Definition eq_of_fn_eq_fn (f : A <~> B) {x y : A} (q : f x = f y) : x = y.
  (left_inv f x)^-1 @ ap f^-1 q @ left_inv f y

Definition eq_of_fn_eq_fn_inv (f : A <~> B) {x y : B} (q : f^-1 x = f^-1 y) : x = y.
  (right_inv f x)^-1 @ ap f q @ right_inv f y

Definition ap_eq_of_fn_eq_fn (f : A <~> B) {x y : A} (q : f x = f y) : ap f (eq_of_fn_eq_fn' f q) = q.
  ap_eq_of_fn_eq_fn' f q

Definition eq_of_fn_eq_fn_ap (f : A <~> B) {x y : A} (q : x = y) : eq_of_fn_eq_fn' f (ap f q) = q.
  eq_of_fn_eq_fn'_ap f q

Definition to_inv_homotopy_inv {f g : A <~> B} (p : f == g) : f^-1ᵉ == g^-1ᵉ.
  inv_homotopy_inv p

  --we need thisDefinition for the funext_of_ua proof
Definition inv_eq {A B : Type} (eqf eqg : A <~> B) (p : eqf = eqg) : (to_fun eqf)^-1 = (to_fun eqg)^-1.
  eq.rec_on p idp

Definition equiv_of_equiv_of_eq [trans] {A B C : Type} (p : A = B) (q : B <~> C) : A <~> C.
  equiv_of_eq p @e q
Definition equiv_of_eq_of_equiv [trans] {A B C : Type} (p : A <~> B) (q : B = C) : A <~> C.
  p @e equiv_of_eq q

Definition equiv_lift (A : Type) : A <~> lift A . equiv.mk up _

Definition equiv_rect (f : A <~> B) (P : B -> Type) (g : forall a, P (f a)) (b : B) : P b.
  right_inv f b # g (f^-1 b)

Definition equiv_rect' (f : A <~> B) (P : A -> B -> Type) (g : forall b, P (f^-1 b) b) (a : A) : P a (f a).
  left_inv f a # g (f a)

Definition equiv_rect_comp (f : A <~> B) (P : B -> Type)
      (df : forall (x : A), P (f x)) (x : A) : equiv_rect f P df (f x) = df x.
    calc
      equiv_rect f P df (f x)
            = right_inv f (f x) # df (f^-1 (f x))   : by esimp
        ... = ap f (left_inv f x) # df (f^-1 (f x)) : by rewrite -adj
        ... = left_inv f x # df (f^-1 (f x))        : by rewrite -tr_compose
        ... = df x                                 : by rewrite (apdt df (left_inv f x))
Defined.

  section

  variables {A B : Type} (f : A <~> B) {a : A} {b : B}
Definition to_eq_of_eq_inv (p : a = f^-1 b) : f a = b.
  ap f p @ right_inv f b

Definition to_eq_of_inv_eq (p : f^-1 b = a) : b = f a.
  (eq_of_eq_inv p^-1)^-1

Definition to_inv_eq_of_eq (p : b = f a) : f^-1 b = a.
  ap f^-1 p @ left_inv f a

Definition to_eq_inv_of_eq (p : f a = b) : a = f^-1 b.
  (inv_eq_of_eq p^-1)^-1

Defined.

  section

  variables {A : Type} {B C : A -> Type} (f : forall {a}, B a <~> C a)
            {g : A -> A} {g' : A -> A} (h : forall {a}, B (g' a) -> B (g a)) (h' : forall {a}, C (g' a) -> C (g a))

Definition inv_commute (p : forall (a : A) (b : B (g' a)), f (h b) = h' (f b)) {a : A}
    (c : C (g' a)) : f^-1 (h' c) = h (f^-1 c).
  inv_commute' @f @h @h' p c

Definition fun_commute_of_inv_commute (p : forall , f^-1 (h' c) = h (f^-1 c))
    {a : A} (b : B (g' a)) : f (h b) = h' (f b).
  fun_commute_of_inv_commute' @f @h @h' p b

Definition inv_commute1 {B C : Type} (f : B <~> C) (h : B -> B) (h' : C -> C)
    (p : forall (b : B), f (h b) =   h' (f b)) (c : C) : f^-1 (h' c) = h (f^-1 c).
  inv_commute1' (to_fun f) h h' p c

Defined.

  infixl ` @pe `:75 . equiv_of_equiv_of_eq
  infixl ` @ep `:75 . equiv_of_eq_of_equiv

Defined. equiv

open equiv
namespace is_equiv

Definition is_equiv_of_equiv_of_homotopy {A B : Type} (f : A <~> B)
    {f' : A -> B} (Hty : f == f') : is_equiv f'.
  @(homotopy_closed f) f' _ Hty

Defined. is_equiv

export [unfold] equiv
export [unfold] is_equiv
