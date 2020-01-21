(*
Copyright (c) 2015 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz
*)

import ..function

open eq is_equiv function

namespace arrow

  structure arrow.
    (dom : Type)
    (cod : Type)
    (arrow : dom -> cod)

  abbreviation dom . @arrow.dom
  abbreviation cod . @arrow.cod

Definition arrow_of_fn {A B : Type} (f : A -> B) : arrow.
  arrow.mk A B f

  structure morphism (A B : Type).
    (mor : A -> B)

Definition morphism_of_arrow [coercion] (f : arrow) : morphism (dom f) (cod f).
  morphism.mk (arrow.arrow f)

  attribute morphism.mor [coercion]

  structure arrow_hom (f g : arrow).
    (on_dom : dom f -> dom g)
    (on_cod : cod f -> cod g)
    (commute : forall (x : dom f), g (on_dom x) = on_cod (f x))

  abbreviation on_dom . @arrow_hom.on_dom
  abbreviation on_cod . @arrow_hom.on_cod
  abbreviation commute . @arrow_hom.commute

  variables {f g : arrow}

Definition on_fiber (r : arrow_hom f g) (y : cod f)
    : fiber f y -> fiber g (on_cod r y).
  fiber.rec (fun x p => fiber.mk (on_dom r x) (commute r x @ ap (on_cod r) p))

  structure is_retraction [class] (r : arrow_hom f g) : Type.
    (sect : arrow_hom g f)
    (right_inverse_dom : forall (a : dom g), on_dom r (on_dom sect a) = a)
    (right_inverse_cod : forall (b : cod g), on_cod r (on_cod sect b) = b)
    (cohere : forall (a : dom g), commute r (on_dom sect a) @ ap (on_cod r) (commute sect a)
                            = ap g (right_inverse_dom a) @ (right_inverse_cod (g a))^-1)

Definition retraction_on_fiber (r : arrow_hom f g) [H : is_retraction r]
    (b : cod g) : fiber f (on_cod (is_retraction.sect r) b) -> fiber g b.
  fiber.rec (fun x q => fiber.mk (on_dom r x) (commute r x @ ap (on_cod r) q @ is_retraction.right_inverse_cod r b))

Definition retraction_on_fiber_right_inverse' (r : arrow_hom f g) [H : is_retraction r]
    (a : dom g) (b : cod g) (p : g a = b)
    : retraction_on_fiber r b (on_fiber (is_retraction.sect r) b (fiber.mk a p)) = fiber.mk a p.
Proof.
    induction p, unfold on_fiber, unfold retraction_on_fiber,
    apply @fiber.fiber_eq _ _ g (g a)
      (fiber.mk
        (on_dom r (on_dom (is_retraction.sect r) a))
        (commute r (on_dom (is_retraction.sect r) a)
          @ ap (on_cod r) (commute (is_retraction.sect r) a)
          @ is_retraction.right_inverse_cod r (g a)))
      (fiber.mk a (refl (g a)))
      (is_retraction.right_inverse_dom r a), (* everything but this field should be inferred *)
    rewrite [is_retraction.cohere r a],
    apply inv_con_cancel_right
Defined.

Definition retraction_on_fiber_right_inverse (r : arrow_hom f g) [H : is_retraction r]
    : forall (b : cod g), forall (z : fiber g b), retraction_on_fiber r b (on_fiber (is_retraction.sect r) b z) = z.
  fun b => fiber.rec (fun a p => retraction_on_fiber_right_inverse' r a b p)

  (* Lemma 4.7.3 *)
Definition retraction_on_fiber_is_retraction [instance] (r : arrow_hom f g) [H : is_retraction r]
    (b : cod g) : _root_.is_retraction (retraction_on_fiber r b).
  _root_.is_retraction.mk (on_fiber (is_retraction.sect r) b) (retraction_on_fiber_right_inverse r b)

  (* Theorem 4.7.4 *)
Definition retract_of_equivalence_is_equivalence (r : arrow_hom f g) [H : is_retraction r]
    [K : is_equiv f] : is_equiv g.
Proof.
    apply @is_equiv_of_is_contr_fun _ _ g =>
    intro b,
    apply is_contr_retract (retraction_on_fiber r b),
    exact is_contr_fun_of_is_equiv f (on_cod (is_retraction.sect r) b)
Defined.

Defined. arrow

namespace arrow
  variables {A B : Type} {f g : A -> B} (p : f == g)

Definition arrow_hom_of_homotopy : arrow_hom (arrow_of_fn f) (arrow_of_fn g).
  arrow_hom.mk id id (fun x => (p x)^-1)

Definition is_retraction_arrow_hom_of_homotopy [instance]
    : is_retraction (arrow_hom_of_homotopy p).
  is_retraction.mk
    (arrow_hom_of_homotopy (fun x => (p x)^-1))
    (fun a => idp)
    (fun b => idp)
    (fun a => con_eq_of_eq_inv_con (ap_id _))

Defined. arrow

namespace arrow
  (*
    equivalences in the arrow category; could be packaged into structures.
    cannot be moved to types.pi because of the dependence on types.equiv.
  *)

  variables {A A' B B' : Type} (f : A -> B) (f' : A' -> B')
            (α : A -> A') (β : B -> B')
            [Hf : is_equiv f] [Hf' : is_equiv f']
  include Hf Hf'

  open function
Definition inv_commute_of_commute (p : f' o α == β o f) : f'^-1 o β == α o f^-1.
Proof.
    apply inv_homotopy_of_homotopy_post f' (α o f^-1) β,
    apply homotopy.symm,
    apply inv_homotopy_of_homotopy_pre f (f' o α) β,
    apply p
Defined.

Definition inv_commute_of_commute_top (p : f' o α == β o f) (a : A)
    : inv_commute_of_commute f f' α β p (f a)
    =  (ap f'^-1 (p a))^-1 @ left_inv f' (α a) @ ap α (left_inv f a)^-1.
Proof.
    unfold inv_commute_of_commute,
    unfold inv_homotopy_of_homotopy_post,
    unfold inv_homotopy_of_homotopy_pre,
    rewrite [adj f a,-(ap_compose β f)],
    rewrite [eq_of_square (natural_square p (left_inv f a))],
    rewrite [ap_inv f'^-1,ap_con f'^-1,con_inv,con.assoc,con.assoc],
    apply whisker_left (ap f'^-1 (p a))^-1,
    apply eq_of_square, rewrite [ap_inv α,-(ap_compose f'^-1 (f' o α))],
    apply hinverse, rewrite [ap_compose (f'^-1 o f') α],
    refine vconcat_eq _ (ap_id (ap α (left_inv f a))),
    apply natural_square_tr (left_inv f') (ap α (left_inv f a))
Defined.

Definition ap_bot_inv_commute_of_commute (p : f' o α == β o f) (b : B)
    : ap f' (inv_commute_of_commute f f' α β p b)
    = right_inv f' (β b) @ ap β (right_inv f b)^-1 @ (p (f^-1 b))^-1.
Proof.
    unfold inv_commute_of_commute,
    unfold inv_homotopy_of_homotopy_post,
    unfold inv_homotopy_of_homotopy_pre,
    rewrite [ap_con,-(ap_compose f' f'^-1),-(adj f' (α (f^-1 b)))],
    rewrite [con.assoc (right_inv f' (β b)) (ap β (right_inv f b)^-1)
                       (p (f^-1 b))^-1],
    apply eq_of_square,
    refine vconcat_eq _
      (whisker_right (p (f^-1 b))^-1 (ap_inv β (right_inv f b)))^-1,
    refine vconcat_eq _
      (con_inv (p (f^-1 b)) (ap β (right_inv f b))),
    refine vconcat_eq _
      (ap_id (p (f^-1 b) @ ap β (right_inv f b))^-1),
    apply natural_square_tr (right_inv f')
      (p (f^-1 b) @ ap β (right_inv f b))^-1
Defined.

Definition is_equiv_inv_commute_of_commute
    : is_equiv (inv_commute_of_commute f f' α β).
Proof.
    unfold inv_commute_of_commute,
    apply @is_equiv_compose _ _ _ (inv_homotopy_of_homotopy_post f' (α o f^-1) β)
      (homotopy.symm o (inv_homotopy_of_homotopy_pre f (f' o α) β)),
    { apply @is_equiv_compose _ _ _ homotopy.symm (inv_homotopy_of_homotopy_pre f (f' o α) β),
      { apply inv_homotopy_of_homotopy_pre.is_equiv },
      { apply pi.is_equiv_homotopy_symm }
    },
    { apply inv_homotopy_of_homotopy_post.is_equiv }
Defined.
Defined. arrow
