(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about embeddings and surjections
*)

import hit.trunc types.equiv cubical.square types.nat

open equiv sigma sigma.ops eq trunc is_trunc pi is_equiv fiber prod pointed nat

variables {A B C : Type} (f f' : A -> B) {b : B}

(* the image of a map is the (-1)-truncated fiber *)
Definition image' (f : A -> B) (b : B) : Type . ∥ fiber f b ∥
Definition is_prop_image' [instance] (f : A -> B) (b : B) : is_prop (image' f b) . !is_trunc_trunc
Definition image (f : A -> B) (b : B) : Prop . Prop.mk (image' f b) _

Definition total_image {A B : Type} (f : A -> B) : Type . sigma (image f)

Definition is_embedding [class] (f : A -> B) . forall (a a' : A), is_equiv (ap f : a = a' -> f a = f a')

Definition is_surjective [class] (f : A -> B) . forall (b : B), image f b

Definition is_split_surjective [class] (f : A -> B) . forall (b : B), fiber f b

structure is_retraction [class] (f : A -> B).
  (sect : B -> A)
  (right_inverse : forall (b : B), f (sect b) = b)

structure is_section [class] (f : A -> B).
  (retr : B -> A)
  (left_inverse : forall (a : A), retr (f a) = a)

Definition is_weakly_constant [class] (f : A -> B) . forall (a a' : A), f a = f a'

structure is_constant [class] (f : A -> B).
  ((point _) : B)
  (eq : forall (a : A), f a = (point _))

structure is_conditionally_constant [class] (f : A -> B).
  (g : ∥A∥ -> B)
  (eq : forall (a : A), f a = g (tr a))

section image
protectedDefinition image.mk {f : A -> B} {b : B} (a : A) (p : f a = b)
  : image f b.
tr (fiber.mk a p)

protectedDefinition image.rec {f : A -> B} {b : B} {P : image' f b -> Type}
  [H : forall v, is_prop (P v)] (H : forall (a : A) (p : f a = b), P (image.mk a p)) (v : image' f b) : P v.
Proof. unfold [image'] at *, induction v with v, induction v with a p, exact H a p end

Definition image.elim {A B : Type} {f : A -> B} {C : Type} [is_prop C] {b : B}
  (H : image f b) (H' : ∀ (a : A), f a = b -> C) : C.
Proof.
  refine (trunc.elim _ H),
  intro H'', cases H'' with a Ha, exact H' a Ha
Defined.

Definition image.equiv_exists {A B : Type} {f : A -> B} {b : B} : image f b <~> ∃ a, f a = b.
trunc_equiv_trunc _ (fiber.sigma_char _ _)

Definition image_pathover {f : A -> B} {x y : B} (p : x = y) (u : image f x) (v : image f y) :
  u =[p] v.
!is_prop.elimo

(* total_image.elim_set is in hit.prop_trunc to avoid dependency cycle *)

Defined. image

namespace function

  abbreviation sect          . @is_retraction.sect
  abbreviation right_inverse . @is_retraction.right_inverse
  abbreviation retr          . @is_section.retr
  abbreviation left_inverse  . @is_section.left_inverse

Definition is_equiv_ap_of_embedding [instance] [H : is_embedding f] (a a' : A)
  : is_equiv (ap f : a = a' -> f a = f a').
  H a a'

Definition ap_inv_idp {a : A} {H : is_equiv (ap f : a = a -> f a = f a)}
  : (ap f)^-1ᶠ idp = idp :> a = a.
  !left_inv

  variable {f}
Definition is_injective_of_is_embedding [H : is_embedding f] {a a' : A}
  : f a = f a' -> a = a'.
  (ap f)^-1

Definition is_embedding_of_is_injective [HA : is_set A] [HB : is_set B]
  (H : forall (a a' : A), f a = f a' -> a = a') : is_embedding f.
Proof.
  intro a a',
  fapply adjointify,
  {exact (H a a')},
  {intro p, apply is_set.elim},
  {intro p, apply is_set.elim}
Defined.

  variable (f)

Definition is_prop_is_embedding [instance] : is_prop (is_embedding f).
  by unfold is_embedding; exact _

Definition is_embedding_equiv_is_injective [HA : is_set A] [HB : is_set B]
  : is_embedding f <~> (forall (a a' : A), f a = f a' -> a = a').
Proof.
  fapply equiv.MK,
  { apply @is_injective_of_is_embedding},
  { apply is_embedding_of_is_injective},
  { intro H, apply is_prop.elim},
  { intro H, apply is_prop.elim, }
Defined.

Definition is_prop_fiber_of_is_embedding [H : is_embedding f] (b : B) :
  is_prop (fiber f b).
Proof.
  apply is_prop.mk, intro v w,
  induction v with a p, induction w with a' q, induction q,
  fapply fiber_eq,
  { esimp, apply is_injective_of_is_embedding p},
  { esimp [is_injective_of_is_embedding], symmetry, apply right_inv}
Defined.

Definition is_prop_fun_of_is_embedding [H : is_embedding f] : is_trunc_fun -1 f.
  is_prop_fiber_of_is_embedding f

Definition is_embedding_of_is_prop_fun [H : is_trunc_fun -1 f] : is_embedding f.
Proof.
  intro a a', fapply adjointify,
  { intro p, exact ap point (@is_prop.elim (fiber f (f a')) _ (fiber.mk a p) (fiber.mk a' idp))},
  { intro p, rewrite [-ap_compose], esimp, apply ap_con_eq (@point_eq _ _ f (f a'))},
  { intro p, induction p, apply ap (ap point), apply is_prop_elim_self}
Defined.

  variable {f}
Definition is_surjective_rec_on {P : Type} (H : is_surjective f) (b : B) [Pt : is_prop P]
  (IH : fiber f b -> P) : P.
  trunc.rec_on (H b) IH
  variable (f)

Definition is_surjective_of_is_split_surjective [instance] [H : is_split_surjective f]
  : is_surjective f.
  fun b => tr (H b)

Definition is_prop_is_surjective [instance] : is_prop (is_surjective f).
Proof. unfold is_surjective, exact _ end

Definition is_surjective_cancel_right {A B C : Type} (g : B -> C) (f : A -> B)
  [H : is_surjective (g o f)] : is_surjective g.
Proof.
  intro c,
  induction H c with a p,
  exact tr (fiber.mk (f a) p)
Defined.

Definition is_weakly_constant_ap [instance] [H : is_weakly_constant f] (a a' : A) :
  is_weakly_constant (ap f : a = a' -> f a = f a').
  take p q : a = a',
  have forall {b c : A} {r : b = c}, (H a b)^-1 @ H a c = ap f r, from
  (fun b c r => eq.rec_on r (con_Vp _)),
  this^-1 @ this

Definition is_constant_ap [instance] [H : is_constant f] (a a' : A)
  : is_constant (ap f : a = a' -> f a = f a').
Proof.
  induction H with b q,
  fapply is_constant.mk,
  { exact q a @ (q a')^-1},
  { intro p, induction p, exact (con_pV _)^-1}
Defined.

Definition is_contr_is_retraction [instance] [H : is_equiv f] : is_contr (is_retraction f).
Proof.
  have H2 : (Σ(g : B -> A), forall b, f (g b) = b) <~> is_retraction f,
Proof.
  fapply equiv.MK,
  {intro x, induction x with g p, constructor, exact p},
  {intro h, induction h, apply sigma.mk, assumption},
  {intro h, induction h, reflexivity},
  {intro x, induction x, reflexivity},
Defined.,
  apply is_trunc_equiv_closed, exact H2,
  apply is_equiv.is_contr_right_inverse
Defined.

Definition is_contr_is_section [instance] [H : is_equiv f] : is_contr (is_section f).
Proof.
  have H2 : (Σ(g : B -> A), forall a, g (f a) = a) <~> is_section f,
Proof.
  fapply equiv.MK,
  {intro x, induction x with g p, constructor, exact p},
  {intro h, induction h, apply sigma.mk, assumption},
  {intro h, induction h, reflexivity},
  {intro x, induction x, reflexivity},
Defined.,
  apply is_trunc_equiv_closed, exact H2,
  fapply is_trunc_equiv_closed,
  {apply sigma_equiv_sigma_right, intro g, apply eq_equiv_homotopy},
  fapply is_trunc_equiv_closed,
  {apply fiber.sigma_char},
  fapply is_contr_fiber_of_is_equiv,
  exact to_is_equiv (arrow_equiv_arrow_left_rev A (equiv.mk f H)),
Defined.

Definition is_embedding_of_is_equiv [instance] [H : is_equiv f] : is_embedding f.
  fun a a' => _

Definition is_equiv_of_is_surjective_of_is_embedding
  [H : is_embedding f] [H' : is_surjective f] : is_equiv f.
  @is_equiv_of_is_contr_fun _ _ _
  (fun b => is_surjective_rec_on H' b
  (fun a => is_contr.mk a
  (fun a' =>
  fiber_eq ((ap f)^-1 ((point_eq a) @ (point_eq a')^-1))
  (by rewrite (right_inv (ap f)); rewrite inv_con_cancel_right))))

Definition is_split_surjective_of_is_retraction [H : is_retraction f] : is_split_surjective f.
  fun b => fiber.mk (sect f b) (right_inverse f b)

Definition is_constant_compose_point [instance] (b : B)
  : is_constant (f o point : fiber f b -> B).
  is_constant.mk b (fun v => by induction v with a p;exact p)

Definition is_embedding_of_is_prop_fiber [H : forall (b : B), is_prop (fiber f b)] : is_embedding f.
  is_embedding_of_is_prop_fun _

Definition is_retraction_of_is_equiv [instance] [H : is_equiv f] : is_retraction f.
  is_retraction.mk f^-1 (right_inv f)

Definition is_section_of_is_equiv [instance] [H : is_equiv f] : is_section f.
  is_section.mk f^-1 (left_inv f)

Definition is_equiv_of_is_section_of_is_retraction [H1 : is_retraction f] [H2 : is_section f]
  : is_equiv f.
  let g . sect f in let h . retr f in
  adjointify f
  g
  (right_inverse f)
  (fun a => calc
  g (f a) = h (f (g (f a))) : left_inverse
  ... = h (f a) : right_inverse f
  ... = a : left_inverse)

  section
  local attribute is_equiv_of_is_section_of_is_retraction [instance] [priority 10000]
  local attribute trunctype.struct [instance] [priority 1] (* remove after #842 is closed *)
  variable (f)
Definition is_prop_is_retraction_prod_is_section : is_prop (is_retraction f \* is_section f).
Proof.
  apply is_prop_of_imp_is_contr, intro H, induction H with H1 H2,
  exact _,
Defined.
Defined.

Definition is_retraction_trunc_functor [instance] (r : A -> B) [H : is_retraction r]
  (n : trunc_index) : is_retraction (trunc_functor n r).
  is_retraction.mk
  (trunc_functor n (sect r))
  (fun b =>
  ((trunc_functor_compose n (sect r) r) b)^-1
  @ trunc_homotopy n (right_inverse r) b
  @ trunc_functor_id n B b)

  (* Lemma 3.11.7 *)
Definition is_contr_retract (r : A -> B) [H : is_retraction r] : is_contr A -> is_contr B.
Proof.
  intro CA,
  apply is_contr.mk (r (center A)),
  intro b,
  exact ap r (center_eq (is_retraction.sect r b)) @ (is_retraction.right_inverse r b)
Defined.

  local attribute is_prop_is_retraction_prod_is_section [instance]
Definition is_retraction_prod_is_section_equiv_is_equiv
  : (is_retraction f \* is_section f) <~> is_equiv f.
Proof.
  apply equiv_of_is_prop,
  intro H, induction H, apply is_equiv_of_is_section_of_is_retraction,
  intro H, split, repeat exact _
Defined.

Definition is_retraction_equiv_is_split_surjective :
  is_retraction f <~> is_split_surjective f.
Proof.
  fapply equiv.MK,
  { intro H, induction H with g p, intro b, constructor, exact p b},
  { intro H, constructor, intro b, exact point_eq (H b)},
  { intro H, esimp, apply eq_of_homotopy, intro b, esimp, induction H b, reflexivity},
  { intro H, induction H with g p, reflexivity},
Defined.

Definition is_embedding_compose (g : B -> C) (f : A -> B)
  (H₁ : is_embedding g) (H₂ : is_embedding f) : is_embedding (g o f).
Proof.
  intros, apply @(is_equiv.homotopy_closed (ap g o ap f)),
  { apply is_equiv_compose},
  symmetry, exact ap_compose g f
Defined.

Definition is_surjective_compose (g : B -> C) (f : A -> B)
  (H₁ : is_surjective g) (H₂ : is_surjective f) : is_surjective (g o f).
Proof.
  intro c, induction H₁ c with b p, induction H₂ b with a q,
  exact image.mk a (ap g q @ p)
Defined.

Definition is_split_surjective_compose (g : B -> C) (f : A -> B)
  (H₁ : is_split_surjective g) (H₂ : is_split_surjective f) : is_split_surjective (g o f).
Proof.
  intro c, induction H₁ c with b p, induction H₂ b with a q,
  exact fiber.mk a (ap g q @ p)
Defined.

Definition is_injective_compose (g : B -> C) (f : A -> B)
  (H₁ : forall (b b'), g b = g b' -> b = b') (H₂ : forall (a a'), f a = f a' -> a = a')
  (a a' : A) (p : g (f a) = g (f a')) : a = a'.
  H₂ (H₁ p)

Definition is_embedding_pr1 [instance] {A : Type} (B : A -> Type) [H : forall a, is_prop (B a)]
  : is_embedding (@pr1 A B).
  fun v v' => to_is_equiv (sigma_eq_equiv v v' @e !sigma_equiv_of_is_contr_right)

  variables {f f'}
Definition is_embedding_homotopy_closed (p : f == f') (H : is_embedding f) : is_embedding f'.
Proof.
  intro a a', fapply is_equiv_of_equiv_of_homotopy,
  exact equiv.mk (ap f) _ @e equiv_eq_closed_left _ (p a) @e equiv_eq_closed_right _ (p a'),
  intro q, esimp, exact (eq_bot_of_square (transpose (natural_square p q)))^-1
Defined.

Definition is_embedding_homotopy_closed_rev (p : f' == f) (H : is_embedding f) : is_embedding f'.
  is_embedding_homotopy_closed p^-1ʰᵗʸ H

Definition is_surjective_homotopy_closed (p : f == f') (H : is_surjective f) : is_surjective f'.
Proof.
  intro b, induction H b with a q,
  exact image.mk a ((p a)^-1 @ q)
Defined.

Definition is_surjective_homotopy_closed_rev (p : f' == f) (H : is_surjective f) :
  is_surjective f'.
  is_surjective_homotopy_closed p^-1ʰᵗʸ H

Definition is_equiv_ap1_gen_of_is_embedding {A B : Type} (f : A -> B) [is_embedding f]
  {a a' : A} {b b' : B} (q : f a = b) (q' : f a' = b') : is_equiv (ap1_gen f q q').
Proof.
  induction q, induction q',
  exact is_equiv.homotopy_closed _ (ap1_gen_idp_left f)^-1ʰᵗʸ,
Defined.

Definition is_equiv_ap1_of_is_embedding {A B : pType} (f : A ->* B) [is_embedding f] :
  is_equiv (Ω-> f).
  is_equiv_ap1_gen_of_is_embedding f (point_eq f) (point_eq f)

Definition loop_pequiv_loop_of_is_embedding {A B : pType} (f : A ->* B)
  [is_embedding f] : loops A <~>* loops B.
  pequiv_of_pmap (Ω-> f) (is_equiv_ap1_of_is_embedding f)

Definition loopn_pequiv_loopn_of_is_embedding (n : ℕ) [H : is_succ n]
  {A B : pType} (f : A ->* B) [is_embedding f] : Ω[n] A <~>* Ω[n] B.
Proof.
  induction H with n,
  exact !loopn_succ_in @e*
  loopn_pequiv_loopn n (loop_pequiv_loop_of_is_embedding f) @e*
  !loopn_succ_in^-1ᵉ*
Defined.

  (*
  TheDefinitions
  is_surjective_of_is_equiv
  is_equiv_equiv_is_embedding_times_is_surjective
  are in types.trunc

  See types.arrow_2 for retractions
  *)

Defined. function
