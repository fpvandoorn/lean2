(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about pullbacks
*)

import cubical.square
open eq equiv is_equiv function prod unit is_trunc sigma

variables {A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ : Type}
          (f₁₀ : A₀₀ -> A₂₀) (f₃₀ : A₂₀ -> A₄₀)
          (f₀₁ : A₀₀ -> A₀₂) (f₂₁ : A₂₀ -> A₂₂) (f₄₁ : A₄₀ -> A₄₂)
          (f₁₂ : A₀₂ -> A₂₂) (f₃₂ : A₂₂ -> A₄₂)

structure pullback (f₂₁ : A₂₀ -> A₂₂) (f₁₂ : A₀₂ -> A₂₂).
  (pr1 : A₂₀)
  (pr2 : A₀₂)
  (pr1_pr2 : f₂₁ pr1 = f₁₂ pr2)

namespace pullback

  protectedDefinition sigma_char :
    pullback f₂₁ f₁₂ <~> Σ(a₂₀ : A₂₀) (a₀₂ : A₀₂), f₂₁ a₂₀ = f₁₂ a₀₂.
Proof.
    fapply equiv.MK,
    { intro x, induction x with a₂₀ a₀₂ p, exact ⟨a₂₀, a₀₂, p⟩},
    { intro x, induction x with a₂₀ y, induction y with a₀₂ p, exact pullback.mk a₂₀ a₀₂ p},
    { intro x, induction x with a₂₀ y, induction y with a₀₂ p, reflexivity},
    { intro x, induction x with a₂₀ a₀₂ p, reflexivity},
Defined.

  variables {f₁₀ f₃₀ f₀₁ f₂₁ f₄₁ f₁₂ f₃₂}

Definition pullback_corec (p : forall a, f₂₁ (f₁₀ a) = f₁₂ (f₀₁ a)) (a : A₀₀)
    : pullback f₂₁ f₁₂.
  pullback.mk (f₁₀ a) (f₀₁ a) (p a)

Definition pullback_eq {x y : pullback f₂₁ f₁₂} (p1 : pr1 x = pr1 y) (p2 : pr2 x = pr2 y)
    (r : square (pr1_pr2 x) (pr1_pr2 y) (ap f₂₁ p1) (ap f₁₂ p2)) : x = y.
  by induction y; induction x; esimp at *; induction p1; induction p2;
     exact ap (pullback.mk _ _) (eq_of_vdeg_square r)

Definition pullback_comm_equiv : pullback f₁₂ f₂₁ <~> pullback f₂₁ f₁₂.
Proof.
    fapply equiv.MK,
    { intro v, induction v with x y p, exact pullback.mk y x p^-1},
    { intro v, induction v with x y p, exact pullback.mk y x p^-1},
    { intro v, induction v, esimp, exact ap _ !inv_inv},
    { intro v, induction v, esimp, exact ap _ !inv_inv},
Defined.

Definition pullback_unit_equiv
    : pullback (fun (x : A₀₂) => star) (fun (x : A₂₀) => star) <~> A₀₂ \* A₂₀.
Proof.
    fapply equiv.MK,
    { intro v, induction v with x y p, exact (x, y)},
    { intro v, induction v with x y, exact pullback.mk x y idp},
    { intro v, induction v, reflexivity},
    { intro v, induction v, esimp, apply ap _ !is_prop.elim},
Defined.

Definition pullback_along {f : A₂₀ -> A₂₂} (g : A₀₂ -> A₂₂) : pullback f g -> A₂₀.
  pr1

  postfix `^*`:(max+1) . pullback_along

  variables (f₁₀ f₃₀ f₀₁ f₂₁ f₄₁ f₁₂ f₃₂)

  structure pullback_square (f₁₀ : A₀₀ -> A₂₀) (f₁₂ : A₀₂ -> A₂₂) (f₀₁ : A₀₀ -> A₀₂) (f₂₁ : A₂₀ -> A₂₂)
    : Type.
    (comm : forall a, f₂₁ (f₁₀ a) = f₁₂ (f₀₁ a))
    (is_pullback : is_equiv (pullback_corec comm : A₀₀ -> pullback f₂₁ f₁₂))

  attribute pullback_square.is_pullback [instance]
Definition pbs_comm . @pullback_square.comm

Definition pullback_square_pullback
    : pullback_square (pr1 : pullback f₂₁ f₁₂ -> A₂₀) f₁₂ pr2 f₂₁.
  pullback_square.mk
    pr1_pr2
    (adjointify _ (fun f => f)
                  (fun f => by induction f; reflexivity)
                  (fun g => by induction g; reflexivity))

  variables {f₁₀ f₃₀ f₀₁ f₂₁ f₄₁ f₁₂ f₃₂}

Definition pullback_square_equiv (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
    : A₀₀ <~> pullback f₂₁ f₁₂.
  equiv.mk _ (pullback_square.is_pullback s)

Definition of_pullback (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
    (x : pullback f₂₁ f₁₂) : A₀₀.
  (pullback_square_equiv s)^-1 x

Definition right_of_pullback (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
    (x : pullback f₂₁ f₁₂) : f₁₀ (of_pullback s x) = pr1 x.
  ap pr1 (to_right_inv (pullback_square_equiv s) x)

Definition down_of_pullback (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
    (x : pullback f₂₁ f₁₂) : f₀₁ (of_pullback s x) = pr2 x.
  ap pr2 (to_right_inv (pullback_square_equiv s) x)

  (*Definition pullback_square_compose_inverse (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁) *)
  (*   (t : pullback_square f₃₀ f₃₂ f₂₁ f₄₁) (x : pullback f₄₁ (f₃₂ o f₁₂)) : A₀₀ . *)
  (* let a₂₀' : pullback f₄₁ f₃₂ . *)
  (*   pullback.mk (pr1 x) (f₁₂ (pr2 x)) (pr1_pr2 x) in *)
  (* let a₂₀ : A₂₀ . *)
  (*   of_pullback t a₂₀' in *)
  (* have a₀₀' : pullback f₂₁ f₁₂, *)
  (*   from pullback.mk a₂₀ (pr2 x) !down_of_pullback, *)
  (* show A₀₀, *)
  (*   from of_pullback s a₀₀' *)
  (* local attribute pullback_square_compose_inverse *)

  (*Definition down_psci (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁) *)
  (*   (t : pullback_square f₃₀ f₃₂ f₂₁ f₄₁) (x : pullback f₄₁ (f₃₂ o f₁₂)) : *)
  (*    f₀₁ (pullback_square_compose_inverse s t x) = pr2 x . *)
  (* by apply down_of_pullback *)

  (*Definition pullback_square_compose (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁) *)
  (*   (t : pullback_square f₃₀ f₃₂ f₂₁ f₄₁) : pullback_square (f₃₀ o f₁₀) (f₃₂ o f₁₂) f₀₁ f₄₁ . *)
  (* pullback_square.mk *)
  (*   (fun a => pbs_comm t (f₁₀ a) @ ap f₃₂ (pbs_comm s a)) *)
  (*   (adjointify _ *)
  (*     (pullback_square_compose_inverse s t) *)
  (*     begin *)
  (*       intro x, induction x with x y p, esimp, *)
  (*       fapply pullback_eq: esimp, *)
  (*       { exact ap f₃₀ !right_of_pullback @ !right_of_pullback}, *)
  (*       { apply down_of_pullback}, *)
  (*       { esimp, exact sorry } *)
  (*     end *)
  (*     begin *)
  (*       intro x, esimp, exact sorry *)
  (*     end) *)

Defined. pullback
