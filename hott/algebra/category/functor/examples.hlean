(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Definition of functors involving at least two different constructions of categories
*)

import ..constructions.functor ..constructions.product ..constructions.opposite
       ..constructions.set

open category nat_trans eq prod prod.ops

namespace functor

  section
  open iso equiv
  variables {C D E : Precategory} (F F' : C \*c D ⇒ E) (G G' : C ⇒ E ^c D)
  (* currying a functor *)
Definition functor_curry_ob (c : C) : D ⇒ E.
  F of (constant_functor D c \*f 1)

Definition functor_curry_hom (c c' : C) (f : c ⟶ c')
    : functor_curry_ob F c ⟹ functor_curry_ob F c'.
  F ofn (constant_nat_trans D f \*n 1)

  local abbreviation Fhom . @functor_curry_hom

Definition functor_curry_id (c : C) : Fhom F (ID c) = 1.
  nat_trans_eq (fun d => respect_id F (c, d))

Definition functor_curry_comp (c c' c'' : C) (f' : c' ⟶ c'') (f : c ⟶ c')
    : Fhom F (f' o f) = Fhom F f' on Fhom F f.
Proof.
    apply nat_trans_eq,
    intro d, calc
    natural_map (Fhom F (f' o f)) d = F (f' o f, id) : by esimp
      ... = F (f' o f, category.id o category.id)    : by rewrite id_id
      ... = F ((f',id) o (f, id))                    : by esimp
      ... = F (f',id) o F (f, id)                    : by rewrite [respect_comp F]
      ... = natural_map ((Fhom F f') o (Fhom F f)) d : by esimp
Defined.

Definition functor_curry : C ⇒ E ^c D.
  functor.mk (functor_curry_ob F)
             (functor_curry_hom F)
             (functor_curry_id F)
             (functor_curry_comp F)

  (* currying a functor => flipping the arguments *)
Definition functor_curry_rev_ob (d : D) : C ⇒ E.
  F of (1 \*f constant_functor C d)

Definition functor_curry_rev_hom (d d' : D) (g : d ⟶ d')
    : functor_curry_rev_ob F d ⟹ functor_curry_rev_ob F d'.
  F ofn (1 \*n constant_nat_trans C g)

  local abbreviation Fhomr . @functor_curry_rev_hom
Definition functor_curry_rev_id (d : D) : Fhomr F (ID d) = nat_trans.id.
  nat_trans_eq (fun c => respect_id F (c, d))

Definition functor_curry_rev_comp (d d' d'' : D) (g' : d' ⟶ d'') (g : d ⟶ d')
    : Fhomr F (g' o g) = Fhomr F g' on Fhomr F g.
Proof.
    apply nat_trans_eq, esimp, intro c, rewrite [-id_id at {1}], apply respect_comp F
Defined.

Definition functor_curry_rev : D ⇒ E ^c C.
  functor.mk (functor_curry_rev_ob F)
             (functor_curry_rev_hom F)
             (functor_curry_rev_id F)
             (functor_curry_rev_comp F)

  (* uncurrying a functor *)

Definition functor_uncurry_ob (p : C \*c D) : E.
  to_fun_ob (G p.1) p.2

Definition functor_uncurry_hom (p p' : C \*c D) (f : hom p p')
    : functor_uncurry_ob G p ⟶ functor_uncurry_ob G p' .
  to_fun_hom (to_fun_ob G p'.1) f.2 o natural_map (to_fun_hom G f.1) p.2
  local abbreviation Ghom . @functor_uncurry_hom

Definition functor_uncurry_id (p : C \*c D) : Ghom G (ID p) = id.
  calc
    Ghom G (ID p) = to_fun_hom (to_fun_ob G p.1) id o natural_map (to_fun_hom G id) p.2 : by esimp
      ... = id o natural_map (to_fun_hom G id) p.2 : by rewrite respect_id
      ... = id o natural_map nat_trans.id p.2      : by rewrite respect_id
      ... = id                                     : id_id

Definition functor_uncurry_comp (p p' p'' : C \*c D) (f' : p' ⟶ p'') (f : p ⟶ p')
    : Ghom G (f' o f) = Ghom G f' o Ghom G f.
  calc
    Ghom G (f' o f)
          = to_fun_hom (to_fun_ob G p''.1) (f'.2 o f.2) o natural_map (to_fun_hom G (f'.1 o f.1)) p.2 : by esimp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 o to_fun_hom (to_fun_ob G p''.1) f.2)
              o natural_map (to_fun_hom G (f'.1 o f.1)) p.2                : by rewrite respect_comp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 o to_fun_hom (to_fun_ob G p''.1) f.2)
              o natural_map (to_fun_hom G f'.1 o to_fun_hom G f.1) p.2     : by rewrite respect_comp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 o to_fun_hom (to_fun_ob G p''.1) f.2)
             o (natural_map (to_fun_hom G f'.1) p.2 o natural_map (to_fun_hom G f.1) p.2) : by esimp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 o natural_map (to_fun_hom G f'.1) p'.2)
              o (to_fun_hom (to_fun_ob G p'.1) f.2 o natural_map (to_fun_hom G f.1) p.2) :
                  by rewrite [square_prepostcompose (!naturality^-1ᵖ) _ _]
      ... = Ghom G f' o Ghom G f : by esimp

Definition functor_uncurry : C \*c D ⇒ E.
  functor.mk (functor_uncurry_ob G)
             (functor_uncurry_hom G)
             (functor_uncurry_id G)
             (functor_uncurry_comp G)

Definition functor_uncurry_functor_curry : functor_uncurry (functor_curry F) = F.
  functor_eq (fun p => ap (to_fun_ob F) !prod.eta)
Proof.
    intro cd cd' fg,
    cases cd with c d, cases cd' with c' d', cases fg with f g,
    transitivity to_fun_hom (functor_uncurry (functor_curry F)) (f => g),
    apply id_leftright,
    show (functor_uncurry (functor_curry F)) (f => g) = F (f,g),
      from calc
        (functor_uncurry (functor_curry F)) (f => g)
              = to_fun_hom F (id => g) o to_fun_hom F (f => id) : by esimp
          ... = F (category.id o f, g o category.id)        : (respect_comp F (id,g) (f,id))^-1
          ... = F (f, g o category.id)                      : by rewrite id_left
          ... = F (f,g)                                     : by rewrite id_right,
Defined.

Definition functor_curry_functor_uncurry_ob (c : C)
    : functor_curry (functor_uncurry G) c = G c.
Proof.
    fapply functor_eq =>
     { intro d, reflexivity},
     { intro d d' g, refine !id_leftright @ _, esimp,
       rewrite [▸*, ↑functor_uncurry_hom => respect_id, ▸*, id_right]}
Defined.

Definition functor_curry_functor_uncurry : functor_curry (functor_uncurry G) = G.
Proof.
    fapply functor_eq => exact (functor_curry_functor_uncurry_ob G) =>
    intro c c' f,
    fapply nat_trans_eq,
    intro d,
    apply concat,
      {apply (ap (fun x => x o _)),
        apply concat, apply natural_map_hom_of_eq, apply (ap hom_of_eq), apply ap010_functor_eq} =>
    apply concat,
       {apply (ap (fun x => _ o x)), apply (ap (fun x => _ o x)),
         apply concat, apply natural_map_inv_of_eq,
         apply (ap (fun x => hom_of_eq x^-1)), apply ap010_functor_eq} =>
    apply concat, apply id_leftright,
    apply concat, apply (ap (fun x => x o _)), apply respect_id,
    apply id_left
Defined.

  (*
     This only states that the carriers of (C ^ D) ^ E and C ^ (E \* D) are equivalent.
     In [exponential laws] we prove that these are in fact isomorphic categories
  *)
Definition prod_functor_equiv_functor_functor (C D E : Precategory)
    : (C \*c D ⇒ E) <~> (C ⇒ E ^c D).
  equiv.MK functor_curry
           functor_uncurry
           functor_curry_functor_uncurry
           functor_uncurry_functor_curry

  variables {F F' G G'}
Definition nat_trans_curry_nat (η : F ⟹ F') (c : C)
    : functor_curry_ob F c ⟹ functor_curry_ob F' c.
Proof.
    fapply nat_trans.mk: esimp,
    { intro d, exact η (c, d)},
    { intro d d' f, apply naturality}
Defined.

Definition nat_trans_curry (η : F ⟹ F')
    : functor_curry F ⟹ functor_curry F'.
Proof.
    fapply nat_trans.mk: esimp,
    { exact nat_trans_curry_nat η},
    { intro c c' f, apply nat_trans_eq, intro d, esimp, apply naturality}
Defined.

Definition nat_trans_uncurry (η : G ⟹ G')
    : functor_uncurry G ⟹ functor_uncurry G'.
Proof.
    fapply nat_trans.mk: esimp,
    { intro v, unfold functor_uncurry_ob => exact (η v.1) v.2},
    { intro v w f, unfold functor_uncurry_hom =>
      rewrite [-assoc, ap010 natural_map (naturality η f.1) v.2, assoc, naturality, -assoc]}
Defined.
Defined.

  section
  open is_trunc

  (* hom-functors *)

Definition hom_functor_assoc {C : Precategory} {a1 a2 a3 a4 a5 a6 : C}
    (f1 : hom a5 a6) (f2 : hom a4 a5) (f3 : hom a3 a4) (f4 : hom a2 a3) (f5 : hom a1 a2)
      : (f1 o f2) o f3 o (f4 o f5) = f1 o (f2 o f3 o f4) o f5.
  calc
        _ = f1 o f2 o f3 o f4 o f5     : by rewrite -assoc
      ... = f1 o (f2 o f3) o f4 o f5   : by rewrite -assoc
      ... = f1 o ((f2 o f3) o f4) o f5 : by rewrite -(assoc (f2 o f3) _ _)
      ... = _                          : by rewrite (assoc f2 f3 f4)

  (* the functor hom(- =>-) *)
Definition hom_functor.{u v} (C : Precategory.{u v}) : Cᵒᵖ \*c C ⇒ set.{v}.
  functor.mk
    (fun (x : Cᵒᵖ \*c C) => @homset (Cᵒᵖ) C x.1 x.2)
    (fun (x y : Cᵒᵖ \*c C) (f : @category.precategory.hom (Cᵒᵖ \*c C) (Cᵒᵖ \*c C) x y)
       (h : @homset (Cᵒᵖ) C x.1 x.2), f.2 o[C] (h o[C] f.1))
    (fun x => abstract @eq_of_homotopy _ _ _ (ID (@homset Cᵒᵖ C x.1 x.2))
            (fun h => concat (by apply @id_left) (by apply @id_right)) end)
    (fun x y z g f => abstract eq_of_homotopy (by intros; apply @hom_functor_assoc) end)

  (* the functor hom(- => c) *)
Definition hom_functor_left.{u v} {C : Precategory.{u v}} (c : C)
    : Cᵒᵖ ⇒ set.{v}.
  functor_curry_rev_ob !hom_functor c

  (* the functor hom(c => -) *)
Definition hom_functor_right.{u v} {C : Precategory.{u v}} (c : C)
    : C ⇒ set.{v}.
  functor_curry_ob !hom_functor c

Definition nat_trans_hom_functor_left {C : Precategory}
    (c c' : C) (f : c ⟶ c') : hom_functor_left c ⟹ hom_functor_left c'.
  functor_curry_rev_hom !hom_functor f

  (* the yoneda embedding itself is defined in [yoneda]. *)
Defined.



Defined. functor
