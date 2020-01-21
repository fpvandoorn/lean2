(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Comma category
*)

import ..functor.basic ..strict ..category

open eq functor equiv sigma sigma.ops is_trunc iso is_equiv

namespace category

  structure comma_object {A B C : Precategory} (S : A ⇒ C) (T : B ⇒ C).
    (a : A)
    (b : B)
    (f : S a ⟶ T b)
  abbreviation ob1 . @comma_object.a
  abbreviation ob2 . @comma_object.b
  abbreviation mor . @comma_object.f

  variables {A B C : Precategory} (S : A ⇒ C) (T : B ⇒ C)

Definition comma_object_sigma_char : (Σ(a : A) (b : B), S a ⟶ T b) <~> comma_object S T.
Proof.
    fapply equiv.MK,
    { intro u, exact comma_object.mk u.1 u.2.1 u.2.2},
    { intro x, cases x with a b f, exact ⟨a, b, f⟩},
    { intro x, cases x, reflexivity},
    { intro u, cases u with u1 u2, cases u2, reflexivity},
Defined.

Definition is_trunc_comma_object (n : trunc_index) [HA : is_trunc n A]
    [HB : is_trunc n B] [H : forall (s d : C), is_trunc n (hom s d)] : is_trunc n (comma_object S T).
  by apply is_trunc_equiv_closed;apply comma_object_sigma_char

  variables {S T}
Definition comma_object_eq' {x y : comma_object S T} (p : ob1 x = ob1 y) (q : ob2 x = ob2 y)
    (r : mor x =[ap011 (@hom C C) (ap (to_fun_ob S) p) (ap (to_fun_ob T) q)] mor y) : x = y.
Proof.
    cases x with a b f, cases y with a' b' f', cases p, cases q,
    esimp [ap011,congr,ap,subst] at r,
    eapply (idp_rec_on r), reflexivity
Defined.

  --TODO: remove. This is a different version where Hq is not in square brackets
  (*Definition eq_comp_inverse_of_comp_eq' {ob : Type} {C : precategory ob} {d c b : ob} {r : hom c d} *)
  (*   {q : hom b c} {x : hom b d} {Hq : is_iso q} (p : r o q = x) : r = x o q^-1ʰ . *)
  (* sorry *)
  (* . sorry --eq_inverse_comp_of_comp_eq p *)

Definition comma_object_eq {x y : comma_object S T} (p : ob1 x = ob1 y) (q : ob2 x = ob2 y)
    (r : T (hom_of_eq q) o mor x o S (inv_of_eq p) = mor y) : x = y.
Proof.
    cases x with a b f, cases y with a' b' f', cases p, cases q,
    apply ap (comma_object.mk a' b'),
    rewrite [▸* at r, -r, +respect_id, id_leftright]
Defined.

Definition ap_ob1_comma_object_eq' (x y : comma_object S T) (p : ob1 x = ob1 y) (q : ob2 x = ob2 y)
    (r : mor x =[ap011 (@hom C C) (ap (to_fun_ob S) p) (ap (to_fun_ob T) q)] mor y)
    : ap ob1 (comma_object_eq' p q r) = p.
Proof.
    cases x with a b f, cases y with a' b' f', cases p, cases q,
    eapply (idp_rec_on r), reflexivity
Defined.

Definition ap_ob2_comma_object_eq' (x y : comma_object S T) (p : ob1 x = ob1 y) (q : ob2 x = ob2 y)
    (r : mor x =[ap011 (@hom C C) (ap (to_fun_ob S) p) (ap (to_fun_ob T) q)] mor y)
    : ap ob2 (comma_object_eq' p q r) = q.
Proof.
    cases x with a b f, cases y with a' b' f', cases p, cases q,
    eapply (idp_rec_on r), reflexivity
Defined.

  structure comma_morphism (x y : comma_object S T).
  mk' ::
    (g : ob1 x ⟶ ob1 y)
    (h : ob2 x ⟶ ob2 y)
    (p : T h o mor x = mor y o S g)
    (p' : mor y o S g = T h o mor x)
  abbreviation mor1 . @comma_morphism.g
  abbreviation mor2 . @comma_morphism.h
  abbreviation coh  . @comma_morphism.p
  abbreviation coh' . @comma_morphism.p'

  protectedDefinition comma_morphism.mk [reducible]
    {x y : comma_object S T} (g h p) : comma_morphism x y.
  comma_morphism.mk' g h p p^-1

  variables (x y z w : comma_object S T)
Definition comma_morphism_sigma_char :
    (Σ(g : ob1 x ⟶ ob1 y) (h : ob2 x ⟶ ob2 y), T h o mor x = mor y o S g) <~> comma_morphism x y.
Proof.
    fapply equiv.MK,
    { intro u, exact (comma_morphism.mk u.1 u.2.1 u.2.2)},
    { intro f, cases f with g h p p', exact ⟨g, h, p⟩},
    { intro f, cases f with g h p p', esimp,
      apply ap (comma_morphism.mk' g h p), apply is_prop.elim},
    { intro u, cases u with u1 u2, cases u2 with u2 u3, reflexivity},
Defined.

Definition is_trunc_comma_morphism (n : trunc_index) [H1 : is_trunc n (ob1 x ⟶ ob1 y)]
    [H2 : is_trunc n (ob2 x ⟶ ob2 y)] [Hp : forall m1 m2, is_trunc n (T m2 o mor x = mor y o S m1)]
    : is_trunc n (comma_morphism x y).
  by apply is_trunc_equiv_closed; apply comma_morphism_sigma_char

  variables {x y z w}
Definition comma_morphism_eq {f f' : comma_morphism x y}
    (p : mor1 f = mor1 f') (q : mor2 f = mor2 f') : f = f'.
Proof.
    cases f with g h p₁ p₁', cases f' with g' h' p₂ p₂', cases p, cases q,
    apply ap011 (comma_morphism.mk' g' h'),
      apply is_prop.elim,
      apply is_prop.elim
Defined.

Definition comma_compose (g : comma_morphism y z) (f : comma_morphism x y) : comma_morphism x z.
  comma_morphism.mk
    (mor1 g o mor1 f)
    (mor2 g o mor2 f)
    (by rewrite [+respect_comp,-assoc,coh,assoc,coh,-assoc])

  local infix ` oo `:60 . comma_compose

Definition comma_id : comma_morphism x x.
  comma_morphism.mk id id (by rewrite [+respect_id,id_left,id_right])

Definition comma_assoc (h : comma_morphism z w) (g : comma_morphism y z) (f : comma_morphism x y) :
    h oo (g oo f) = (h oo g) oo f.
  comma_morphism_eq !assoc !assoc

Definition comma_id_left (f : comma_morphism x y) : comma_id oo f = f.
  comma_morphism_eq !id_left !id_left

Definition comma_id_right (f : comma_morphism x y) : f oo comma_id = f.
  comma_morphism_eq !id_right !id_right

  variables (S T)
Definition comma_category : Precategory.
  precategory.MK (comma_object S T)
                 comma_morphism
                 (fun a b => !is_trunc_comma_morphism)
                 (@comma_compose _ _ _ _ _)
                 (@comma_id _ _ _ _ _)
                 (@comma_assoc _ _ _ _ _)
                 (@comma_id_left _ _ _ _ _)
                 (@comma_id_right _ _ _ _ _)

  --TODO: thisDefinition doesn't use category structure of A and B
Definition strict_precategory_comma [HA : strict_precategory A] [HB : strict_precategory B] :
    strict_precategory (comma_object S T).
  strict_precategory.mk (comma_category S T) !is_trunc_comma_object

(*
  --set_option pp.notation false
Definition is_univalent_comma (HA : is_univalent A) (HB : is_univalent B)
    : is_univalent (comma_category S T).
Proof.
    intros c d,
    fapply adjointify,
    { intro i, cases i with f s, cases s with g l r, cases f with fA fB fp, cases g with gA gB gp,
      esimp at *, fapply comma_object_eq,
        {apply iso_of_eq^-1ᶠ, exact (iso.MK fA gA (ap mor1 l) (ap mor1 r))},
        {apply iso_of_eq^-1ᶠ, exact (iso.MK fB gB (ap mor2 l) (ap mor2 r))},
        { apply sorry (*rewrite hom_of_eq_eq_of_iso,*) }},
    { apply sorry},
    { apply sorry},
Defined.
*)

Defined. category
