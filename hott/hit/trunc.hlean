(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

n-truncation of types.

Ported from Coq HoTT
*)

(* The hit n-truncation is primitive, declared in init.hit. *)

import types.sigma types.pointed

open is_trunc eq equiv is_equiv function prod sum sigma

namespace trunc

  protectedDefinition elim {n : trunc_index} {A : Type} {P : Type}
  [Pt : is_trunc n P] (H : A -> P) : trunc n A -> P.
  trunc.rec H

  protectedDefinition elim_on {n : trunc_index} {A : Type} {P : Type} (aa : trunc n A)
  [Pt : is_trunc n P] (H : A -> P) : P.
  trunc.elim H aa

Defined. trunc





namespace trunc

  variables {X Y Z : Type} {P : X -> Type} (n : trunc_index) (A B : Type)

  local attribute is_trunc_eq [instance]

  variables {A n}
Definition untrunc_of_is_trunc [H : is_trunc n A] : trunc n A -> A.
  trunc.rec id

  variables (A n)
Definition is_equiv_tr [instance] [H : is_trunc n A] : is_equiv (@tr n A).
  adjointify _
  (untrunc_of_is_trunc)
  (fun aa => trunc.rec_on aa (fun a => idp))
  (fun a => idp)

Definition trunc_equiv [H : is_trunc n A] : trunc n A <~> A.
  (equiv.mk tr _)^-1ᵉ

Definition is_trunc_of_is_equiv_tr [H : is_equiv (@tr n A)] : is_trunc n A.
  is_trunc_is_equiv_closed n (@tr n _)^-1

  (* Functoriality *)
Definition trunc_functor (f : X -> Y) : trunc n X -> trunc n Y.
  fun xx => trunc.rec_on xx (fun x => tr (f x))

Definition trunc_functor_compose (f : X -> Y) (g : Y -> Z)
  : trunc_functor n (g o f) == trunc_functor n g o trunc_functor n f.
  fun xx => trunc.rec_on xx (fun x => idp)

Definition trunc_functor_id : trunc_functor n (@id A) == id.
  fun xx => trunc.rec_on xx (fun x => idp)

Definition trunc_functor_cast {X Y : Type} (n : ℕ₋₂) (p : X = Y) :
  trunc_functor n (cast p) == cast (ap (trunc n) p).
Proof.
  intro x, induction x with x, esimp,
  exact fn_tr_eq_tr_fn p (fun y => tr) x @ !tr_compose
Defined.

Definition is_equiv_trunc_functor (f : X -> Y) [H : is_equiv f]
  : is_equiv (trunc_functor n f).
  adjointify _
  (trunc_functor n f^-1)
  (fun yy => trunc.rec_on yy (fun y => ap tr !right_inv))
  (fun xx => trunc.rec_on xx (fun x => ap tr !left_inv))

Definition trunc_homotopy {f g : X -> Y} (p : f == g) : trunc_functor n f == trunc_functor n g.
  fun xx => trunc.rec_on xx (fun x => ap tr (p x))

  section
Definition trunc_equiv_trunc (f : X <~> Y) : trunc n X <~> trunc n Y.
  equiv.mk _ (is_equiv_trunc_functor n f)
Defined.

  section
  open prod.ops
Definition trunc_prod_equiv : trunc n (X \* Y) <~> trunc n X \* trunc n Y.
Proof.
  fapply equiv.MK,
  {exact (fun pp => trunc.rec_on pp (fun p => (tr p.1, tr p.2)))},
  {intro p, cases p with xx yy,
  apply (trunc.rec_on xx), intro x,
  apply (trunc.rec_on yy), intro y, exact (tr (x,y))},
  {intro p, cases p with xx yy,
  apply (trunc.rec_on xx), intro x,
  apply (trunc.rec_on yy), intro y, apply idp},
  {intro pp, apply (trunc.rec_on pp), intro p, cases p, apply idp}
Defined.
Defined.

  (* Propositional truncation *)

Definition ttrunc (n : ℕ₋₂) (X : Type) : n-Type.
  trunctype.mk (trunc n X) _

  (* should this live in Prop? *)
Definition merely (A : Type) : Prop . ttrunc -1 A

  notation `||`:max A `||`:0 . merely A
  notation `∥`:max A `∥`:0   . merely A

Definition Exists (P : X -> Type) : Prop . ∥ sigma P ∥
Definition or (A B : Type) : Prop . ∥ A ⊎ B ∥

  notation `exists` binders `,` r:(scoped P, Exists P) . r
  notation `∃` binders `,` r:(scoped P, Exists P) . r
  notation A ` \/ ` B . or A B
  notation A ∨ B    . or A B

Definition merely.intro   (a : A) : ∥ A ∥             . tr a
Definition exists.intro   (x : X) (p : P x) : ∃x, P x . tr ⟨x, p⟩
Definition or.intro_left  (x : X) : X ∨ Y             . tr (inl x)
Definition or.intro_right (y : Y) : X ∨ Y             . tr (inr y)

Definition exists.elim {A : Type} {p : A -> Type} {B : Type} [is_prop B] (H : Exists p)
  (H' : ∀ (a : A), p a -> B) : B.
  trunc.elim (sigma.rec H') H

Definition is_contr_of_merely_prop [H : is_prop A] (aa : merely A) : is_contr A.
  is_contr_of_inhabited_prop (trunc.rec_on aa id)

  section
  open sigma.ops
Definition trunc_sigma_equiv : trunc n (Σ x, P x) <~> trunc n (Σ x, trunc n (P x)).
  equiv.MK (fun pp => trunc.rec_on pp (fun p => tr ⟨p.1, tr p.2⟩))
  (fun pp => trunc.rec_on pp (fun p => trunc.rec_on p.2 (fun b => tr ⟨p.1, b⟩)))
  (fun pp => trunc.rec_on pp (fun p => sigma.rec_on p (fun a bb => trunc.rec_on bb (fun b => by esimp))))
  (fun pp => trunc.rec_on pp (fun p => sigma.rec_on p (fun a b => by esimp)))

Definition trunc_sigma_equiv_of_is_trunc [H : is_trunc n X]
  : trunc n (Σ x, P x) <~> Σ x, trunc n (P x).
  calc
  trunc n (Σ x, P x) <~> trunc n (Σ x, trunc n (P x)) : trunc_sigma_equiv
  ... <~> Σ x, trunc n (P x) : !trunc_equiv
Defined.

  (* the (non-dependent) universal property *)
Definition trunc_arrow_equiv [H : is_trunc n B] :
  (trunc n A -> B) <~> (A -> B).
Proof.
  fapply equiv.MK,
  { intro g a, exact g (tr a)},
  { intro f x, exact trunc.rec_on x f},
  { intro f, apply eq_of_homotopy, intro a, reflexivity},
  { intro g, apply eq_of_homotopy, intro x, exact trunc.rec_on x (fun a => idp)},
Defined.

Defined. trunc
