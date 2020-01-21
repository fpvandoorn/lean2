(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Functors preserving limits
*)

import .colimits ..functor.yoneda ..functor.adjoint

open eq functor yoneda is_trunc nat_trans

namespace category

  variables {I C D : Precategory} {F : I ⇒ C} {G : C ⇒ D}

  (* notions of preservation of limits *)
Definition preserves_limits_of_shape [class] (G : C ⇒ D) (I : Precategory)
    [H : has_limits_of_shape C I].
  forall (F : I ⇒ C), is_terminal (cone_obj_compose G (limit_cone F))

Definition preserves_existing_limits_of_shape [class] (G : C ⇒ D) (I : Precategory).
  forall (F : I ⇒ C) [H : has_terminal_object (cone F)],
    is_terminal (cone_obj_compose G (terminal_object (cone F)))

Definition preserves_existing_limits [class] (G : C ⇒ D).
  forall (I : Precategory) (F : I ⇒ C) [H : has_terminal_object (cone F)],
    is_terminal (cone_obj_compose G (terminal_object (cone F)))

Definition preserves_limits [class] (G : C ⇒ D) [H : is_complete C].
  forall (I : Precategory) [H : has_limits_of_shape C I] (F : I ⇒ C),
    is_terminal (cone_obj_compose G (limit_cone F))

Definition preserves_chosen_limits_of_shape [class] (G : C ⇒ D) (I : Precategory)
    [H : has_limits_of_shape C I] [H : has_limits_of_shape D I].
  forall (F : I ⇒ C), cone_obj_compose G (limit_cone F) = limit_cone (G of F)

Definition preserves_chosen_limits [class] (G : C ⇒ D)
    [H : is_complete C] [H : is_complete D].
  forall (I : Precategory) (F : I ⇒ C), cone_obj_compose G (limit_cone F) = limit_cone (G of F)

  (* basic instances *)
Definition preserves_limits_of_shape_of_preserves_limits [instance] (G : C ⇒ D)
    (I : Precategory) [H : is_complete C] [H : preserves_limits G]
    : preserves_limits_of_shape G I . H I

Definition preserves_chosen_limits_of_shape_of_preserves_chosen_limits [instance] (G : C ⇒ D)
    (I : Precategory) [H : is_complete C] [H : is_complete D] [K : preserves_chosen_limits G]
    : preserves_chosen_limits_of_shape G I . K I

  (* yoneda preserves existing limits *)

  local attribute category.to_precategory

Definition preserves_existing_limits_yoneda_embedding_lemma
    (y : cone_obj F)
    [H : is_terminal y] {G : Cᵒᵖ ⇒ cset} (η : constant_functor I G ⟹ ɏ of F) :
    G ⟹ hom_functor_left (cone_to_obj y).
Proof.
    fapply nat_trans.mk: esimp,
    { intro c x, fapply to_hom_limit,
      { intro i, exact η i c x},
      { exact abstract begin
        intro i j k,
        exact !id_right^-1 @ !assoc^-1 @ ap0100 natural_map (naturality η k) c x end end
        }},
      (* [BUG] abstracting here creates multiple lemmas proving this fact *)
    { intro c c' f, apply eq_of_homotopy, intro x,
      rewrite [id_left], apply to_eq_hom_limit, intro i,
      refine !assoc @ _, rewrite to_hom_limit_commute,
      refine _ @ ap10 (naturality (η i) f) x, rewrite [▸*, id_left]}
      (* abstracting here fails *)
Defined.

Definition preserves_existing_limits_yoneda_embedding (C : Precategory)
    : preserves_existing_limits (yoneda_embedding C).
Proof.
    intro I F H Gη, induction H with y H, induction Gη with G η, esimp at *,
    have lem : forall (i : carrier I),
    nat_trans_hom_functor_left (natural_map (cone_to_nat y) i)
      on @preserves_existing_limits_yoneda_embedding_lemma I C F y H G η = natural_map η i,
    begin
        intro i, apply nat_trans_eq, intro c, apply eq_of_homotopy, intro x,
        esimp, refine !assoc @ !id_right @ !to_hom_limit_commute
    end,
    fapply is_contr.mk,
    { fapply cone_hom.mk,
      { exact preserves_existing_limits_yoneda_embedding_lemma y η},
      { exact lem}},
    { intro v, apply cone_hom_eq, esimp, apply nat_trans_eq, esimp, intro c,
      apply eq_of_homotopy, intro x, refine (to_eq_hom_limit _ _)^-1,
      intro i, refine !id_right^-1 @ !assoc^-1 @ _,
      exact ap0100 natural_map (cone_to_eq v i) c x}
Defined.

  (* left adjoint functors preserve limits *)

(*Definition preserves_existing_limits_left_adjoint_lemma {C D : Precategory} (F : C ⇒ D)
    [H : is_left_adjoint F] {I : Precategory} {G : I ⇒ C} (y : cone_obj G) [K : is_terminal y]
    {d : carrier D} (η : constant_functor I d ⟹ F of G) : d ⟶ to_fun_ob F (cone_to_obj y).
Proof.
    let η . unit F, let θ . counit F, exact sorry
Defined.

Definition preserves_existing_limits_left_adjoint {C D : Precategory} (F : C ⇒ D)
    [H : is_left_adjoint F] : preserves_existing_limits F.
Proof.
    intro I G K dη, induction K with y K, induction dη with d η, esimp at *,
    (* have lem : forall (i : carrier I), *)
    (* nat_trans_hom_functor_left (natural_map (cone_to_nat y) i) *)
    (*   on preserves_existing_limits_yoneda_embedding_lemma y η = natural_map η i, *)
    (* { intro i, apply nat_trans_eq, intro c, apply eq_of_homotopy, intro x, *)
    (*     esimp, refine !assoc @ !id_right @ !to_hom_limit_commute}, *)
    fapply is_contr.mk,
    { fapply cone_hom.mk,
      { esimp, exact sorry},
      { exact lem}},
    { intro v, apply cone_hom_eq, esimp, apply nat_trans_eq, esimp, intro c,
      apply eq_of_homotopy, intro x, refine (to_eq_hom_limit _ _)^-1,
      intro i, refine !id_right^-1 @ !assoc^-1 @ _,
      exact ap0100 natural_map (cone_to_eq v i) c x}
Defined.*)


Defined. category
