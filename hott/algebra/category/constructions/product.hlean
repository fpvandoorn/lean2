(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Product precategory and (TODO) category
*)

import ..category ..nat_trans hit.trunc

open eq prod is_trunc functor sigma trunc iso prod.ops nat_trans

namespace category
Definition precategory_prod [instance] (obC obD : Type)
    [C : precategory obC] [D : precategory obD] : precategory (obC \* obD).
  precategory.mk' (fun a b => hom a.1 b.1 \* hom a.2 b.2)
                  (fun a b c g f => (g.1 o f.1, g.2 o f.2))
                  (fun a => (id, id))
                  (fun a b c d h g f => pair_eq !assoc    !assoc   )
                  (fun a b c d h g f => pair_eq !assoc'   !assoc'  )
                  (fun a b f =>         prod_eq !id_left  !id_left )
                  (fun a b f =>         prod_eq !id_right !id_right)
                  (fun a =>             prod_eq !id_id    !id_id)
                  _

Definition Precategory_prod (C D : Precategory) : Precategory.
  precategory.Mk (precategory_prod C D)

  infixr ` \*c `:70 . Precategory_prod

  variables {C C' D D' X : Precategory} {u v : carrier (C \*c D)}

Definition prod_hom_of_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : hom_of_eq (prod_eq p q) = (hom_of_eq p, hom_of_eq q).
  by induction u; induction v; esimp at *; induction p; induction q; reflexivity

Definition prod_inv_of_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : inv_of_eq (prod_eq p q) = (inv_of_eq p, inv_of_eq q).
  by induction u; induction v; esimp at *; induction p; induction q; reflexivity

Definition pr1_hom_of_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : (hom_of_eq (prod_eq p q)).1 = hom_of_eq p.
  by exact ap pr1 !prod_hom_of_eq

Definition pr1_inv_of_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : (inv_of_eq (prod_eq p q)).1 = inv_of_eq p.
  by exact ap pr1 !prod_inv_of_eq

Definition pr2_hom_of_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : (hom_of_eq (prod_eq p q)).2 = hom_of_eq q.
  by exact ap pr2 !prod_hom_of_eq

Definition pr2_inv_of_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : (inv_of_eq (prod_eq p q)).2 = inv_of_eq q.
  by exact ap pr2 !prod_inv_of_eq

Definition pr1_functor : C \*c D ⇒ C.
  functor.mk pr1
             (fun a b => pr1)
             (fun a => idp)
             (fun a b c g f => idp)

Definition pr2_functor : C \*c D ⇒ D.
  functor.mk pr2
             (fun a b => pr2)
             (fun a => idp)
             (fun a b c g f => idp)

Definition functor_prod (F : X ⇒ C) (G : X ⇒ D) : X ⇒ C \*c D.
  functor.mk (fun a =>     pair (F a) (G a))
             (fun a b f => pair (F f) (G f))
             (fun a =>         abstract pair_eq !respect_id   !respect_id   end)
             (fun a b c g f => abstract pair_eq !respect_comp !respect_comp end)

  infixr ` \*f `:70 . functor_prod

Definition prod_functor_eta (F : X ⇒ C \*c D) : pr1_functor of F \*f pr2_functor of F = F.
Proof.
  fapply functor_eq: esimp =>
  { intro e, apply prod_eq: reflexivity},
  { intro e e' f, apply prod_eq: esimp,
    { refine ap (fun x => x o _ o _) !pr1_hom_of_eq @ _,
      refine ap (fun x => _ o _ o x) !pr1_inv_of_eq @ _, esimp,
      apply id_leftright},
    { refine ap (fun x => x o _ o _) !pr2_hom_of_eq @ _,
      refine ap (fun x => _ o _ o x) !pr2_inv_of_eq @ _, esimp,
      apply id_leftright}}
Defined.

Definition pr1_functor_prod (F : X ⇒ C) (G : X ⇒ D) : pr1_functor of (F \*f G) = F.
  functor_eq (fun x => idp)
             (fun x y f => !id_leftright)

Definition pr2_functor_prod (F : X ⇒ C) (G : X ⇒ D) : pr2_functor of (F \*f G) = G.
  functor_eq (fun x => idp)
             (fun x y f => !id_leftright)

  (*Definition universal_property_prod {C D X : Precategory} (F : X ⇒ C) (G : X ⇒ D) *)
  (*   : is_contr (Σ(H : X ⇒ C \*c D), pr1_functor of H = F \* pr2_functor of H = G) . *)
  (* is_contr.mk *)
  (*   ⟨functor_prod F G => (pr1_functor_prod F G => pr2_functor_prod F G)⟩ *)
  (*   begin *)
  (*     intro v, induction v with H w, induction w with p q, *)
  (*     symmetry, fapply sigma_eq: esimp, *)
  (*     { fapply functor_eq => *)
  (*       { intro x, apply prod_eq: esimp, *)
  (*         { exact ap010 to_fun_ob p x} => *)
  (*         { exact ap010 to_fun_ob q x}} => *)
  (*       { intro x y f, apply prod_eq: esimp, *)
  (*         { exact sorry}, *)
  (*         { exact sorry}}}, *)
  (*     { exact sorry} *)
  (*   end *)

Definition prod_functor_prod (F : C ⇒ D) (G : C' ⇒ D') : C \*c C' ⇒ D \*c D'.
  (F of pr1_functor) \*f (G of pr2_functor)

Definition prod_nat_trans {C D D' : Precategory}
    {F F' : C ⇒ D} {G G' : C ⇒ D'} (η : F ⟹ F') (θ : G ⟹ G') : F \*f G ⟹ F' \*f G'.
Proof.
    fapply nat_trans.mk: esimp,
    { intro c, exact (η c, θ c)},
    { intro c c' f, apply prod_eq: esimp:apply naturality}
Defined.

  infixr ` \*n `:70 . prod_nat_trans

Definition prod_flip_functor (C D : Precategory) : C \*c D ⇒ D \*c C.
  functor.mk (fun p => (p.2, p.1))
             (fun p p' h => (h.2, h.1))
             (fun p => idp)
             (fun p p' p'' h' h => idp)

Definition functor_prod_flip_functor_prod_flip (C D : Precategory)
    : prod_flip_functor D C of (prod_flip_functor C D) = functor.id.
Proof.
  fapply functor_eq =>
  { intro p, apply prod.eta},
  { intro p p' h, cases p with c d, cases p' with c' d',
    apply id_leftright}
Defined.

Defined. category
