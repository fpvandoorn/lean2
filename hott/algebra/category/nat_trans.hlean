(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn, Jakob von Raumer
*)

import .functor.basic
open eq category functor is_trunc equiv sigma.ops sigma is_equiv function pi funext iso

structure nat_trans {C : Precategory} {D : Precategory} (F G : C ⇒ D)
  : Type.
 (natural_map : forall (a : C), hom (F a) (G a))
 (naturality : forall {a b : C} (f : hom a b), G f o natural_map a = natural_map b o F f)

namespace nat_trans

  infixl ` ⟹ `:25 . nat_trans (* \= => *)
  variables {B C D E : Precategory} {F G H I : C ⇒ D} {F' G' : D ⇒ E} {F'' G'' : E ⇒ B} {J : C ⇒ C}

  attribute natural_map [coercion]

  protectedDefinition compose (η : G ⟹ H) (θ : F ⟹ G) : F ⟹ H.
  nat_trans.mk
    (fun a => η a o θ a)
    (fun a b f =>
      abstract calc
        H f o (η a o θ a) = (H f o η a) o θ a : by rewrite assoc
                      ... = (η b o G f) o θ a : by rewrite naturality
                      ... = η b o (G f o θ a) : by rewrite assoc
                      ... = η b o (θ b o F f) : by rewrite naturality
                      ... = (η b o θ b) o F f : by rewrite assoc
      end)

  infixr ` on `:60 . nat_trans.compose

Definition compose_def (η : G ⟹ H) (θ : F ⟹ G) (c : C) : (η on θ) c = η c o θ c . idp

  protectedDefinition id {F : C ⇒ D} : nat_trans F F.
  mk (fun a => id) (fun a b f => !id_right @ !id_left^-1)

  protectedDefinition ID (F : C ⇒ D) : nat_trans F F.
  (@nat_trans.id C D F)

  notation 1 . nat_trans.id

Definition constant_nat_trans (C : Precategory) {D : Precategory} {d d' : D}
    (g : d ⟶ d') : constant_functor C d ⟹ constant_functor C d'.
  mk (fun c => g) (fun c c' f => !id_comp_eq_comp_id)

  open iso
Definition naturality_iso_left (η : F ⟹ G) {a b : C} (f : a ≅ b) : η a = (G f)^-1 o η b o F f.
  by apply eq_inverse_comp_of_comp_eq; apply naturality

Definition naturality_iso_right (η : F ⟹ G) {a b : C} (f : a ≅ b) : η b = G f o η a o (F f)^-1.
  by refine _^-1 @ !assoc^-1; apply comp_inverse_eq_of_eq_comp; apply naturality

Definition nat_trans_mk_eq {η₁ η₂ : forall (a : C), hom (F a) (G a)}
    (nat₁ : forall (a b : C) (f : hom a b), G f o η₁ a = η₁ b o F f)
    (nat₂ : forall (a b : C) (f : hom a b), G f o η₂ a = η₂ b o F f)
    (p : η₁ == η₂)
      : nat_trans.mk η₁ nat₁ = nat_trans.mk η₂ nat₂.
  apd011 nat_trans.mk (eq_of_homotopy p) !is_prop.elimo

Definition nat_trans_eq {η₁ η₂ : F ⟹ G} : natural_map η₁ == natural_map η₂ -> η₁ = η₂.
  by induction η₁; induction η₂; apply nat_trans_mk_eq

  protectedDefinition assoc (η₃ : H ⟹ I) (η₂ : G ⟹ H) (η₁ : F ⟹ G) :
      η₃ on (η₂ on η₁) = (η₃ on η₂) on η₁.
  nat_trans_eq (fun a => !assoc)

  protectedDefinition id_left (η : F ⟹ G) : 1 on η = η.
  nat_trans_eq (fun a => !id_left)

  protectedDefinition id_right (η : F ⟹ G) : η on 1 = η.
  nat_trans_eq (fun a => !id_right)

  protectedDefinition sigma_char (F G : C ⇒ D) :
    (Σ (η : forall (a : C), hom (F a) (G a)), forall (a b : C) (f : hom a b), G f o η a = η b o F f) <~>  (F ⟹ G).
Proof.
    fapply equiv.mk,
      (* TODO(Leo): investigate why we need to use rexact in the following line *)
      {intro S, apply nat_trans.mk, rexact (S.2)},
    fapply adjointify,
      intro H,
          fapply sigma.mk,
            intro a, exact (H a),
          intro a b f, exact (naturality H f),
    intro η, apply nat_trans_eq, intro a, apply idp,
    intro S,
    fapply sigma_eq,
    { apply eq_of_homotopy, intro a, apply idp},
    { apply is_prop.elimo}
Defined.

Definition is_set_nat_trans [instance] : is_set (F ⟹ G).
  by apply is_trunc_is_equiv_closed; apply (equiv.to_is_equiv !nat_trans.sigma_char)

Definition change_natural_map (η : F ⟹ G) (f : forall (a : C), F a ⟶ G a)
    (p : forall a, η a = f a) : F ⟹ G.
  nat_trans.mk f (fun a b g => p a # p b # naturality η g)

Definition nat_trans_functor_compose (η : G ⟹ H) (F : E ⇒ C)
    : G of F ⟹ H of F.
  nat_trans.mk
    (fun a => η (F a))
    (fun a b f => naturality η (F f))

Definition functor_nat_trans_compose (F : D ⇒ E) (η : G ⟹ H)
    : F of G ⟹ F of H.
  nat_trans.mk
    (fun a => F (η a))
    (fun a b f => calc
      F (H f) o F (η a) = F (H f o η a) : by rewrite respect_comp
        ... = F (η b o G f)             : by rewrite (naturality η f)
        ... = F (η b) o F (G f)         : by rewrite respect_comp)

Definition nat_trans_id_functor_compose (η : J ⟹ 1) (F : E ⇒ C)
    : J of F ⟹ F.
  nat_trans.mk
    (fun a => η (F a))
    (fun a b f => naturality η (F f))

Definition id_nat_trans_functor_compose (η : 1 ⟹ J) (F : E ⇒ C)
    : F ⟹ J of F.
  nat_trans.mk
    (fun a => η (F a))
    (fun a b f => naturality η (F f))

Definition functor_nat_trans_id_compose (F : C ⇒ D) (η : J ⟹ 1)
    : F of J ⟹ F.
  nat_trans.mk
    (fun a => F (η a))
    (fun a b f => calc
      F f o F (η a) = F (f o η a) : by rewrite respect_comp
        ... = F (η b o J f)       : by rewrite (naturality η f)
        ... = F (η b) o F (J f)   : by rewrite respect_comp)

Definition functor_id_nat_trans_compose (F : C ⇒ D) (η : 1 ⟹ J)
    : F ⟹ F of J.
  nat_trans.mk
    (fun a => F (η a))
    (fun a b f => calc
      F (J f) o F (η a) = F (J f o η a) : by rewrite respect_comp
        ... = F (η b o f)               : by rewrite (naturality η f)
        ... = F (η b) o F f             : by rewrite respect_comp)

  infixr ` onf ` :62 . nat_trans_functor_compose
  infixr ` ofn ` :62 . functor_nat_trans_compose
  infixr ` on1f `:62 . nat_trans_id_functor_compose
  infixr ` o1nf `:62 . id_nat_trans_functor_compose
  infixr ` of1n `:62 . functor_id_nat_trans_compose
  infixr ` ofn1 `:62 . functor_nat_trans_id_compose

Definition nf_fn_eq_fn_nf_pt (η : F ⟹ G) (θ : F' ⟹ G') (c : C)
    : (θ (G c)) o (F' (η c)) = (G' (η c)) o (θ (F c)).
  (naturality θ (η c))^-1

  variable (F')
Definition nf_fn_eq_fn_nf_pt' (η : F ⟹ G) (θ : F'' ⟹ G'') (c : C)
    : (θ (F' (G c))) o (F'' (F' (η c))) = (G'' (F' (η c))) o (θ (F' (F c))).
  (naturality θ (F' (η c)))^-1
  variable {F'}

Definition nf_fn_eq_fn_nf (η : F ⟹ G) (θ : F' ⟹ G')
    : (θ onf G) on (F' ofn η) = (G' ofn η) on (θ onf F).
  nat_trans_eq (fun c => nf_fn_eq_fn_nf_pt η θ c)

Definition fn_n_distrib (F' : D ⇒ E) (η : G ⟹ H) (θ : F ⟹ G)
    : F' ofn (η on θ) = (F' ofn η) on (F' ofn θ).
  nat_trans_eq (fun c => by apply respect_comp)

Definition n_nf_distrib (η : G ⟹ H) (θ : F ⟹ G) (F' : B ⇒ C)
    : (η on θ) onf F' = (η onf F') on (θ onf F').
  nat_trans_eq (fun c => idp)

Definition fn_id (F' : D ⇒ E) : F' ofn nat_trans.ID F = 1.
  nat_trans_eq (fun c => by apply respect_id)

Definition id_nf (F' : B ⇒ C) : nat_trans.ID F onf F' = 1.
  nat_trans_eq (fun c => idp)

Definition id_fn (η : G ⟹ H) (c : C) : (1 ofn η) c = η c.
  idp

Definition nf_id (η : G ⟹ H) (c : C) : (η onf 1) c = η c.
  idp

Definition nat_trans_of_eq (p : F = G) : F ⟹ G.
  nat_trans.mk (fun c => hom_of_eq (ap010 to_fun_ob p c))
               (fun a b f => eq.rec_on p (!id_right @ !id_left^-1))

Definition compose_rev [unfold_full] (θ : F ⟹ G) (η : G ⟹ H) : F ⟹ H . η on θ

Defined. nat_trans



