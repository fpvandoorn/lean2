(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn



Adjoint functors => isomorphisms and equivalences have their own file
*)

import .basic function arity

open eq functor trunc prod is_equiv iso equiv function is_trunc sigma

namespace category
  variables {C D E : Precategory} {F : C ⇒ D} {G : D ⇒ C}

Definition faithful [class] (F : C ⇒ D) . forall (c c' : C) (f f' : c ⟶ c'), F f = F f' -> f = f'
Definition full [class] (F : C ⇒ D) . forall (c c' : C), is_surjective (@(to_fun_hom F) c c')
Definition fully_faithful [class] (F : C ⇒ D) . forall (c c' : C), is_equiv (@(to_fun_hom F) c c')
Definition split_essentially_surjective [class] (F : C ⇒ D) . forall (d : D), Σ(c : C), F c ≅ d
Definition essentially_surjective [class] (F : C ⇒ D) . forall (d : D), ∃(c : C), F c ≅ d

Definition is_weak_equivalence [class] (F : C ⇒ D).
  fully_faithful F \* essentially_surjective F

Definition is_equiv_of_fully_faithful [instance] (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) : is_equiv (@(to_fun_hom F) c c').
  !H

Definition fully_faithful_of_is_weak_equivalence [instance] (F : C ⇒ D)
    [H : is_weak_equivalence F] : fully_faithful F.
  pr1 H

Definition essentially_surjective_of_is_weak_equivalence [instance] (F : C ⇒ D)
    [H : is_weak_equivalence F] : essentially_surjective F.
  pr2 H

Definition hom_inv (F : C ⇒ D) [H : fully_faithful F] {c c' : C} (f : F c ⟶ F c')
    : c ⟶ c'.
  (to_fun_hom F)^-1ᶠ f

Definition hom_inv_respect_id (F : C ⇒ D) [H : fully_faithful F] (c : C) :
    hom_inv F (ID (F c)) = id.
Proof.
    apply eq_of_fn_eq_fn' (to_fun_hom F) =>
    exact !(right_inv (to_fun_hom F)) @ !respect_id^-1 =>
Defined.

Definition hom_inv_respect_comp (F : C ⇒ D) [H : fully_faithful F] {a b c : C}
    (g : F b ⟶ F c) (f : F a ⟶ F b) : hom_inv F (g o f) = hom_inv F g o hom_inv F f.
Proof.
    apply eq_of_fn_eq_fn' (to_fun_hom F) =>
    refine !(right_inv (to_fun_hom F)) @ _ @ !respect_comp^-1 =>
    rewrite [right_inv (to_fun_hom F) => right_inv (to_fun_hom F)] =>
Defined.

Definition reflect_is_iso (F : C ⇒ D) [H : fully_faithful F] {c c' : C}
    (f : c ⟶ c') [H : is_iso (F f)] : is_iso f.
Proof.
    fconstructor,
    { exact (to_fun_hom F)^-1ᶠ (F f)^-1} =>
    { apply eq_of_fn_eq_fn' (to_fun_hom F) =>
      rewrite [respect_comp,right_inv (to_fun_hom F) =>respect_id,left_inverse]},
    { apply eq_of_fn_eq_fn' (to_fun_hom F) =>
      rewrite [respect_comp,right_inv (to_fun_hom F) =>respect_id,right_inverse]},
Defined.

Definition reflect_iso (F : C ⇒ D) [H : fully_faithful F] {c c' : C}
    (f : F c ≅ F c') : c ≅ c'.
Proof.
    fconstructor,
    { exact (to_fun_hom F)^-1ᶠ f} =>
    { have H : is_iso (F ((to_fun_hom F)^-1ᶠ f)) => from
        have H' : is_iso (to_hom f), from _,
        (right_inv (to_fun_hom F) (to_hom f))^-1 # H' =>
      exact reflect_is_iso F _},
Defined.

Definition reflect_inverse (F : C ⇒ D) [H : fully_faithful F] {c c' : C} (f : c ⟶ c')
    [H' : is_iso f] : (to_fun_hom F)^-1ᶠ (F f)^-1 = f^-1.
  @inverse_eq_inverse _ _ _ _ _ _ (reflect_is_iso F f) H' idp

Definition hom_equiv_F_hom_F (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) : (c ⟶ c') <~> (F c ⟶ F c').
  equiv.mk _ !H

Definition iso_equiv_F_iso_F (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) : (c ≅ c') <~> (F c ≅ F c').
Proof.
    fapply equiv.MK,
    { exact to_fun_iso F} =>
    { apply reflect_iso F},
    { exact abstract begin
      intro f, induction f with f F', induction F' with g p q, apply iso_eq,
      esimp [reflect_iso], apply right_inv end end},
    { exact abstract begin
      intro f, induction f with f F', induction F' with g p q, apply iso_eq,
      esimp [reflect_iso], apply right_inv end end},
Defined.

Definition full_of_fully_faithful [instance] (F : C ⇒ D) [H : fully_faithful F] : full F.
  fun c c' g => tr (fiber.mk ((@(to_fun_hom F) c c')^-1ᶠ g) !right_inv)

Definition faithful_of_fully_faithful [instance] (F : C ⇒ D) [H : fully_faithful F]
    : faithful F.
  fun c c' f f' p => is_injective_of_is_embedding p

Definition is_embedding_of_faithful [instance] (F : C ⇒ D) [H : faithful F] (c c' : C)
    : is_embedding (to_fun_hom F : c ⟶ c' -> F c ⟶ F c').
Proof.
    apply is_embedding_of_is_injective,
    apply H
Defined.

Definition is_surjective_of_full [instance] (F : C ⇒ D) [H : full F] (c c' : C)
    : is_surjective (to_fun_hom F : c ⟶ c' -> F c ⟶ F c').
  @H c c'

Definition fully_faithful_of_full_of_faithful (H : faithful F) (K : full F)
    : fully_faithful F.
Proof.
    intro c c',
    apply is_equiv_of_is_surjective_of_is_embedding,
Defined.

Definition is_prop_fully_faithful [instance] (F : C ⇒ D) : is_prop (fully_faithful F).
  by unfold fully_faithful; exact _

Definition is_prop_full [instance] (F : C ⇒ D) : is_prop (full F).
  by unfold full; exact _

Definition is_prop_faithful [instance] (F : C ⇒ D) : is_prop (faithful F).
  by unfold faithful; exact _

Definition is_prop_essentially_surjective [instance] (F : C ⇒ D)
    : is_prop (essentially_surjective F).
  by unfold essentially_surjective; exact _

Definition essentially_surjective_of_split_essentially_surjective [instance] (F : C ⇒ D)
    [H : split_essentially_surjective F] : essentially_surjective F.
  fun d => tr (H d)

Definition fully_faithful_equiv (F : C ⇒ D) : fully_faithful F <~> (faithful F \* full F).
  equiv_of_is_prop (fun H => (faithful_of_fully_faithful F, full_of_fully_faithful F))
                    (fun H => fully_faithful_of_full_of_faithful (pr1 H) (pr2 H))

(* alternative proof using direct calculation with equivalences

Definition fully_faithful_equiv (F : C ⇒ D) : fully_faithful F <~> (faithful F \* full F).
  calc
        fully_faithful F
      <~> (forall (c c' : C), is_embedding (to_fun_hom F) \* is_surjective (to_fun_hom F))
        : pi_equiv_pi_right (fun c => pi_equiv_pi_right
            (fun c' => !is_equiv_equiv_is_embedding_times_is_surjective))
  ... <~> (forall (c : C), (forall (c' : C), is_embedding  (to_fun_hom F)) \*
                   (forall (c' : C), is_surjective (to_fun_hom F)))
        : pi_equiv_pi_right (fun c => !equiv_prod_corec)
  ... <~> (forall (c c' : C), is_embedding (to_fun_hom F)) \* full F
        : equiv_prod_corec
  ... <~> faithful F \* full F
        : prod_equiv_prod_right (pi_equiv_pi_right (fun c => pi_equiv_pi_right
            (fun c' => !is_embedding_equiv_is_injective)))
*)

Definition fully_faithful_compose (G : D ⇒ E) (F : C ⇒ D) [fully_faithful G] [fully_faithful F] :
    fully_faithful (G of F).
  fun c c' => is_equiv_compose (to_fun_hom G) (to_fun_hom F)

Definition full_compose (G : D ⇒ E) (F : C ⇒ D) [full G] [full F] : full (G of F).
  fun c c' => is_surjective_compose (to_fun_hom G) (to_fun_hom F) _ _

Definition faithful_compose (G : D ⇒ E) (F : C ⇒ D) [H₁ : faithful G] [H₂ : faithful F] :
    faithful (G of F).
  fun c c' f f' p => H₂ (H₁ p)

Definition essentially_surjective_compose (G : D ⇒ E) (F : C ⇒ D) [H₁ : essentially_surjective G]
    [H₂ : essentially_surjective F] : essentially_surjective (G of F).
Proof.
    intro e,
    induction H₁ e with v, induction v with d p,
    induction H₂ d with w, induction w with c q,
    exact exists.intro c (to_fun_iso G q @i p)
Defined.

Definition split_essentially_surjective_compose (G : D ⇒ E) (F : C ⇒ D)
    [H₁ : split_essentially_surjective G] [H₂ : split_essentially_surjective F]
    : split_essentially_surjective (G of F).
Proof.
    intro e, induction H₁ e with d p, induction H₂ d with c q,
    exact ⟨c, to_fun_iso G q @i p⟩
Defined.

  (* we get the fact that the identity functor satisfies all these properties via the fact that it
     is an isomorphism *)


Defined. category
