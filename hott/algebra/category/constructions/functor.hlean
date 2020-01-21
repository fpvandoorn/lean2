(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Functor precategory and category
*)

import .opposite ..functor.attributes

open eq category is_trunc nat_trans iso is_equiv category.hom trunc

namespace functor

Definition precategory_functor [instance] (D C : Precategory)
    : precategory (functor C D).
  precategory.mk (fun a b => nat_trans a b)
                 (fun a b c g f => nat_trans.compose g f)
                 (fun a => nat_trans.id)
                 (fun a b c d h g f => !nat_trans.assoc)
                 (fun a b f => !nat_trans.id_left)
                 (fun a b f => !nat_trans.id_right)

Definition Precategory_functor (D C : Precategory) : Precategory.
  precategory.Mk (precategory_functor D C)

  infixr ` ^c `:80 . Precategory_functor

  section
  (* we prove that if a natural transformation is pointwise an iso, then it is an iso *)
  variables {C D : Precategory} {F G : C ⇒ D} (η : F ⟹ G) [iso : forall (a : C), is_iso (η a)]
  include iso

Definition nat_trans_inverse : G ⟹ F.
  nat_trans.mk
    (fun c => (η c)^-1)
    (fun c d f =>
    abstract begin
      apply comp_inverse_eq_of_eq_comp,
      transitivity (natural_map η d)^-1 o to_fun_hom G f o natural_map η c =>
        {apply eq_inverse_comp_of_comp_eq, symmetry, apply naturality},
        {apply assoc}
    end end)

Definition nat_trans_left_inverse : nat_trans_inverse η on η = 1.
Proof.
    fapply (apdt011 nat_trans.mk),
      apply eq_of_homotopy, intro c, apply left_inverse,
    apply eq_of_homotopy3, intros, apply is_set.elim
Defined.

Definition nat_trans_right_inverse : η on nat_trans_inverse η = 1.
Proof.
    fapply (apdt011 nat_trans.mk),
      apply eq_of_homotopy, intro c, apply right_inverse,
    apply eq_of_homotopy3, intros, apply is_set.elim
Defined.

Definition is_natural_iso : is_iso η.
  is_iso.mk _ (nat_trans_left_inverse η) (nat_trans_right_inverse η)

  variable (iso)
Definition natural_iso.mk : F ≅ G.
  iso.mk _ (is_natural_iso η)

  omit iso

  variables (F G)
Definition is_natural_inverse (η : forall c, F c ≅ G c)
    (nat : forall (a b : C) (f : hom a b), G f o to_hom (η a) = to_hom (η b) o F f)
    {a b : C} (f : hom a b) : F f o to_inv (η a) = to_inv (η b) o G f.
  let η' : F ⟹ G . nat_trans.mk (fun c => to_hom (η c)) @nat in
  naturality (nat_trans_inverse η') f

Definition is_natural_inverse' (η₁ : forall c, F c ≅ G c) (η₂ : F ⟹ G) (p : η₁ == η₂)
    {a b : C} (f : hom a b) : F f o to_inv (η₁ a) = to_inv (η₁ b) o G f.
  is_natural_inverse F G η₁ abstract fun a b g => (p a)^-1 # (p b)^-1 # naturality η₂ g end f

  variables {F G}
Definition natural_iso.MK
    (η : forall c, F c ⟶ G c) (p : forall (c c' : C) (f : c ⟶ c'), G f o η c = η c' o F f)
    (θ : forall c, G c ⟶ F c) (r : forall c, θ c o η c = id) (q : forall c, η c o θ c = id) : F ≅ G.
  iso.mk (nat_trans.mk η p) (@(is_natural_iso _) (fun c => is_iso.mk (θ c) (r c) (q c)))

Definition natural_iso.mk'
    (η : forall c, F c ≅ G c) (p : forall (c c' : C) (f : c ⟶ c'), G f o to_hom (η c) = to_hom (η c') o F f) :
    F ≅ G.
  natural_iso.MK (fun c => to_hom (η c)) p (fun c => to_inv (η c))
                 (fun c => to_left_inverse (η c)) (fun c => to_right_inverse (η c))

Defined.

  section
  (* and conversely, if a natural transformation is an iso, it is componentwise an iso *)
  variables {A B C D : Precategory} {F G : C ⇒ D} (η : hom F G) [isoη : is_iso η] (c : C)
  include isoη
Definition componentwise_is_iso : is_iso (η c).
  @is_iso.mk _ _ _ _ _ (natural_map η^-1 c) (ap010 natural_map ( left_inverse η) c)
                                           (ap010 natural_map (right_inverse η) c)

  local attribute componentwise_is_iso [instance]

  variable {isoη}
Definition natural_map_inverse : natural_map η^-1 c = (η c)^-1 . idp
  variable [isoη]

Definition naturality_iso {c c' : C} (f : c ⟶ c') : G f = η c' o F f o (η c)^-1.
  calc
    G f = (G f o η c) o (η c)^-1  : by rewrite comp_inverse_cancel_right
    ... = (η c' o F f) o (η c)^-1 : by rewrite naturality
    ... = η c' o F f o (η c)^-1   : by rewrite assoc

Definition naturality_iso' {c c' : C} (f : c ⟶ c') : (η c')^-1 o G f o η c = F f.
  calc
   (η c')^-1 o G f o η c = (η c')^-1 o η c' o F f : by rewrite naturality
                    ... = F f                   : by rewrite inverse_comp_cancel_left

  omit isoη

Definition componentwise_iso (η : F ≅ G) (c : C) : F c ≅ G c.
  iso.mk (natural_map (to_hom η) c)
         (@componentwise_is_iso _ _ _ _ (to_hom η) (struct η) c)

Definition componentwise_iso_id (c : C) : componentwise_iso (iso.refl F) c = iso.refl (F c).
  iso_eq (idpath (ID (F c)))

Definition componentwise_iso_iso_of_eq (p : F = G) (c : C)
    : componentwise_iso (iso_of_eq p) c = iso_of_eq (ap010 to_fun_ob p c).
  eq.rec_on p !componentwise_iso_id

Definition naturality_iso_id {F : C ⇒ C} (η : F ≅ 1) (c : C)
    : componentwise_iso η (F c) = F (componentwise_iso η c).
  comp.cancel_left (to_hom (componentwise_iso η c))
    ((naturality (to_hom η)) (to_hom (componentwise_iso η c)))

Definition natural_map_hom_of_eq (p : F = G) (c : C)
    : natural_map (hom_of_eq p) c = hom_of_eq (ap010 to_fun_ob p c).
  eq.rec_on p idp

Definition natural_map_inv_of_eq (p : F = G) (c : C)
    : natural_map (inv_of_eq p) c = hom_of_eq (ap010 to_fun_ob p c)^-1.
  eq.rec_on p idp

Definition hom_of_eq_compose_right {H : B ⇒ C} (p : F = G)
    : hom_of_eq (ap (fun x => x of H) p) = hom_of_eq p onf H.
  eq.rec_on p idp

Definition inv_of_eq_compose_right {H : B ⇒ C} (p : F = G)
    : inv_of_eq (ap (fun x => x of H) p) = inv_of_eq p onf H.
  eq.rec_on p idp

Definition hom_of_eq_compose_left {H : D ⇒ C} (p : F = G)
    : hom_of_eq (ap (fun x => H of x) p) = H ofn hom_of_eq p.
  by induction p; exact !fn_id^-1

Definition inv_of_eq_compose_left {H : D ⇒ C} (p : F = G)
    : inv_of_eq (ap (fun x => H of x) p) = H ofn inv_of_eq p.
  by induction p; exact !fn_id^-1

Definition assoc_natural (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B)
    : H of (G of F) ⟹ (H of G) of F.
  change_natural_map (hom_of_eq !functor.assoc)
                     (fun a => id)
                     (fun a => !natural_map_hom_of_eq @ ap hom_of_eq !ap010_assoc)

Definition assoc_natural_rev (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B)
    : (H of G) of F ⟹ H of (G of F).
  change_natural_map (inv_of_eq !functor.assoc)
                     (fun a => id)
                     (fun a => !natural_map_inv_of_eq @ ap (fun x => hom_of_eq x^-1) !ap010_assoc)

Definition assoc_iso (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B)
    : H of (G of F) ≅ (H of G) of F.
  iso.MK (assoc_natural H G F) (assoc_natural_rev H G F)
         (nat_trans_eq (fun a => proof !id_id qed)) (nat_trans_eq (fun a => proof !id_id qed))

Definition id_left_natural (F : C ⇒ D) : functor.id of F ⟹ F.
  change_natural_map
    (hom_of_eq !functor.id_left)
    (fun c => id)
    (fun c => by induction F; exact !natural_map_hom_of_eq @ ap hom_of_eq !ap010_functor_mk_eq_constant)


Definition id_left_natural_rev (F : C ⇒ D) : F ⟹ functor.id of F.
  change_natural_map
    (inv_of_eq !functor.id_left)
    (fun c => id)
    (fun c => by induction F; exact !natural_map_inv_of_eq @
                                 ap (fun x => hom_of_eq x^-1) !ap010_functor_mk_eq_constant)

Definition id_right_natural (F : C ⇒ D) : F of functor.id ⟹ F.
  change_natural_map
    (hom_of_eq !functor.id_right)
    (fun c => id)
    (fun c => by induction F; exact !natural_map_hom_of_eq @ ap hom_of_eq !ap010_functor_mk_eq_constant)

Definition id_right_natural_rev (F : C ⇒ D) : F ⟹ F of functor.id.
  change_natural_map
    (inv_of_eq !functor.id_right)
    (fun c => id)
    (fun c => by induction F; exact !natural_map_inv_of_eq @
                                 ap (fun x => hom_of_eq x^-1) !ap010_functor_mk_eq_constant)

Defined.

  section
  variables {C D E : Precategory} {G G' : D ⇒ E} {F F' : C ⇒ D} {J : D ⇒ D}

Definition is_iso_nf_compose (G : D ⇒ E) (η : F ⟹ F') [H : is_iso η]
    : is_iso (G ofn η).
  is_iso.mk
    (G ofn @inverse (C ⇒ D) _ _ _ η _)
    abstract !fn_n_distrib^-1 @ ap (fun x => G ofn x) (@left_inverse  (C ⇒ D) _ _ _ η _)  @ !fn_id end
    abstract !fn_n_distrib^-1 @ ap (fun x => G ofn x) (@right_inverse (C ⇒ D) _ _ _ η _) @ !fn_id end

Definition is_iso_fn_compose (η : G ⟹ G') (F : C ⇒ D) [H : is_iso η]
    : is_iso (η onf F).
  is_iso.mk
    (@inverse (D ⇒ E) _ _ _ η _ onf F)
    abstract !n_nf_distrib^-1 @ ap (fun x => x onf F) (@left_inverse  (D ⇒ E) _ _ _ η _)  @ !id_nf end
    abstract !n_nf_distrib^-1 @ ap (fun x => x onf F) (@right_inverse (D ⇒ E) _ _ _ η _)  @ !id_nf end

Definition functor_iso_compose (G : D ⇒ E) (η : F ≅ F') : G of F ≅ G of F'.
  iso.mk _ (is_iso_nf_compose G (to_hom η))

Definition iso_functor_compose (η : G ≅ G') (F : C ⇒ D) : G of F ≅ G' of F.
  iso.mk _ (is_iso_fn_compose (to_hom η) F)

  infixr ` ofi ` :62 . functor_iso_compose
  infixr ` oif ` :62 . iso_functor_compose


(* TODO: also needs n_nf_distrib and id_nf for these compositions
Definition nidf_compose (η : J ⟹ 1) (F : C ⇒ D) [H : is_iso η]
    : is_iso (η on1f F).
  is_iso.mk
   (@inverse (D ⇒ D) _ _ _ η _ o1nf F)
   abstract _ end
            _

Definition idnf_compose (η : 1 ⟹ J) (F : C ⇒ D) [H : is_iso η]
    : is_iso (η o1nf F).
  is_iso.mk _
            _
            _

Definition fnid_compose (F : D ⇒ E) (η : J ⟹ 1) [H : is_iso η]
    : is_iso (F ofn1 η).
  is_iso.mk _
            _
            _

Definition fidn_compose (F : D ⇒ E) (η : 1 ⟹ J) [H : is_iso η]
    : is_iso (F of1n η).
  is_iso.mk _
            _
            _
*)

Defined.

  namespace functor

    variables {C : Precategory} {D : Category} {F G : D ^c C}
Definition eq_of_iso_ob (η : F ≅ G) (c : C) : F c = G c.
    by apply eq_of_iso; apply componentwise_iso; exact η

    local attribute functor.to_fun_hom [reducible]
Definition eq_of_iso (η : F ≅ G) : F = G.
    begin
    fapply functor_eq =>
      {exact (eq_of_iso_ob η)},
      {intro c c' f,
        esimp [eq_of_iso_ob, inv_of_eq, hom_of_eq, eq_of_iso],
        rewrite [*right_inv iso_of_eq],
        symmetry, apply @naturality_iso _ _ _ _ _ (iso.struct _)
      }
    end

Definition iso_of_eq_eq_of_iso (η : F ≅ G) : iso_of_eq (eq_of_iso η) = η.
    begin
    apply iso_eq,
    apply nat_trans_eq,
    intro c,
    rewrite natural_map_hom_of_eq, esimp [eq_of_iso],
    rewrite ap010_functor_eq => esimp [hom_of_eq,eq_of_iso_ob],
    rewrite (right_inv iso_of_eq),
    end

Definition eq_of_iso_iso_of_eq (p : F = G) : eq_of_iso (iso_of_eq p) = p.
    begin
    apply functor_eq2 =>
    intro c,
    esimp [eq_of_iso],
    rewrite ap010_functor_eq =>
    esimp [eq_of_iso_ob],
    rewrite componentwise_iso_iso_of_eq,
    rewrite (left_inv iso_of_eq)
    end

Definition is_univalent (D : Category) (C : Precategory) : is_univalent (D ^c C).
    fun F G => adjointify _ eq_of_iso
                       iso_of_eq_eq_of_iso
                       eq_of_iso_iso_of_eq

Defined. functor

Definition category_functor [instance] (D : Category) (C : Precategory)
    : category (D ^c C).
  category.mk (D ^c C) (functor.is_univalent D C)

Definition Category_functor (D : Category) (C : Precategory) : Category.
  category.Mk (D ^c C) !category_functor

  --thisDefinition is only useful if the exponent is a category,
  (*  and the elaborator has trouble with inserting the coercion *)
Definition Category_functor' (D C : Category) : Category.
  Category_functor D C

  namespace ops
    infixr ` ^c2 `:35 . Category_functor
Defined. ops

  namespace functor
    variables {C : Precategory} {D : Category} {F G : D ^c C}

Definition eq_of_pointwise_iso (η : F ⟹ G) (iso : forall (a : C), is_iso (η a)) : F = G.
    eq_of_iso (natural_iso.mk η iso)

Definition iso_of_eq_eq_of_pointwise_iso (η : F ⟹ G) (iso : forall (c : C), is_iso (η c))
      : iso_of_eq (eq_of_pointwise_iso η iso) = natural_iso.mk η iso.
   !iso_of_eq_eq_of_iso

Definition hom_of_eq_eq_of_pointwise_iso (η : F ⟹ G) (iso : forall (c : C), is_iso (η c))
      : hom_of_eq (eq_of_pointwise_iso η iso) = η.
   !hom_of_eq_eq_of_iso

Definition inv_of_eq_eq_of_pointwise_iso (η : F ⟹ G) (iso : forall (c : C), is_iso (η c))
      : inv_of_eq (eq_of_pointwise_iso η iso) = nat_trans_inverse η.
   !inv_of_eq_eq_of_iso

Defined. functor

  (*
    functors involving only the functor category
    (see ..functor.curry for some other functors involving also products)
  *)

  variables {C D I : Precategory}
Definition constant2_functor (F : I ⇒ D ^c C) (c : C) : I ⇒ D.
  functor.mk (fun i => to_fun_ob (F i) c)
             (fun i j f => natural_map (F f) c)
             abstract (fun i => ap010 natural_map !respect_id c @ proof idp qed) end
             abstract (fun i j k g f => ap010 natural_map !respect_comp c) end

Definition constant2_functor_natural (F : I ⇒ D ^c C) {c d : C} (f : c ⟶ d)
    : constant2_functor F c ⟹ constant2_functor F d.
  nat_trans.mk (fun i => to_fun_hom (F i) f)
               (fun i j k => (naturality (F k) f)^-1)

Definition functor_flip (F : I ⇒ D ^c C) : C ⇒ D ^c I.
  functor.mk (constant2_functor F)
             @(constant2_functor_natural F)
             abstract begin intros, apply nat_trans_eq, intro i, esimp, apply respect_id end end
             abstract begin intros, apply nat_trans_eq, intro i, esimp, apply respect_comp end end

Definition eval_functor (C D : Precategory) (d : D) : C ^c D ⇒ C.
Proof.
    fapply functor.mk: esimp =>
    { intro F, exact F d},
    { intro G F η, exact η d},
    { intro F, reflexivity},
    { intro H G F η θ, reflexivity},
Defined.

Definition precomposition_functor {C D} (E) (F : C ⇒ D)
    : E ^c D ⇒ E ^c C.
Proof.
    fapply functor.mk: esimp =>
    { intro G, exact G of F},
    { intro G H η, exact η onf F},
    { intro G, reflexivity},
    { intro G H I η θ, reflexivity},
Defined.

Definition faithful_precomposition_functor [instance]
    {C D E} {H : C ⇒ D} [Hs : essentially_surjective H] : faithful (precomposition_functor E H).
Proof.
    intro F G γ δ Hγδ, apply nat_trans_eq, intro b,
    induction Hs b with Hb, induction Hb with a f,
    refine naturality_iso_right γ f @ _ @ (naturality_iso_right δ f)^-1,
    apply ap (fun x => _ o natural_map x a o _) Hγδ,
Defined.

  open sigma sigma.ops
  section fully_faithful_precomposition
  variables {E : Precategory} {H : C ⇒ D} [Hs : essentially_surjective H] [Hf : full H]
    {F G : D ⇒ E} (γ : F of H ⟹ G of H)
  include Hs Hf

  privateDefinition fully_faithful_precomposition_functor_prop [instance] (b) :
    is_prop (Σ g, forall a (f : H a ≅ b), γ a = G f^-1ⁱ o g o F f).
Proof.
    fapply is_prop.mk, intros g h, cases g with g Hg, cases h with h Hh,
    fapply sigma.dpair_eq_dpair,
    { induction Hs b with Hb, induction Hb with a0 f,
      apply comp.cancel_right (F f), apply comp.cancel_left (G f^-1ⁱ),
      apply (Hg a0 f)^-1 @ (Hh a0 f) },
    apply is_prop.elimo
Defined.

  privateDefinition fully_faithful_precomposition_functor_pair (b) :
    Σ g, forall a (f : H a ≅ b), γ a = G f^-1ⁱ o g o F f.
Proof.
    induction Hs b with Hb, induction Hb with a0 h, fconstructor,
    exact G h o γ a0 o F h^-1ⁱ, intro a f,
    induction Hf (to_hom (f @i h^-1ⁱ)) with k Ek,
    have is_iso (H k), by rewrite Ek; apply _,
    refine _ @ !assoc^-1, refine _ @ ap (fun x => x o F f) !assoc^-1, refine _ @ !assoc,
    refine _ @ ap (fun x => (G f^-1ⁱ o G h) o x) !assoc,
    do 2 krewrite [-respect_comp], esimp,
    apply eq_comp_of_inverse_comp_eq,
    exact ap (fun x => G x o γ a) Ek^-1 @ naturality γ k @ ap (fun x => γ a0 o F x) Ek
Defined.

  --TODO speed this up
  privateDefinition fully_faithful_precomposition_naturality {b b' : carrier D}
    (f : hom b b') : to_fun_hom G f o (fully_faithful_precomposition_functor_pair γ b).1
    = (fully_faithful_precomposition_functor_pair γ b').1 o to_fun_hom F f.
Proof.
    esimp[fully_faithful_precomposition_functor_pair] =>
    induction Hs b with Hb, induction Hb with a h,
    induction Hs b' with Hb', induction Hb' with a' h',
    induction Hf (to_hom h'^-1ⁱ o f o to_hom h) with k Ek,
    apply concat, apply assoc,
    apply concat, apply ap (fun x => x o _),
     apply concat, apply !respect_comp^-1,
     apply concat, apply ap (fun x => to_fun_hom G x) => apply inverse,
      apply comp_eq_of_eq_inverse_comp, apply Ek, apply respect_comp,
    apply concat, apply !assoc^-1,
    apply concat, apply ap (fun x => _ o x), apply concat, apply assoc,
     apply concat, apply ap (fun x => x o _), apply naturality γ, apply !assoc^-1,
    apply concat, apply ap (fun x => _ o _ o x), apply concat, esimp, apply !respect_comp^-1,
     apply concat, apply ap (fun x => to_fun_hom F x) =>
      apply comp_inverse_eq_of_eq_comp, apply Ek @ !assoc, apply respect_comp,
    apply concat, apply assoc, apply concat, apply assoc,
    apply ap (fun x => x o _) !assoc^-1
Defined.

Definition fully_faithful_precomposition_functor [instance] :
    fully_faithful (precomposition_functor E H).
Proof.
    apply fully_faithful_of_full_of_faithful,
    { apply faithful_precomposition_functor } =>
    { intro F G γ, esimp at *, fapply image.mk,
      fconstructor,
      { intro b, apply (fully_faithful_precomposition_functor_pair γ b).1 } =>
      { intro b b' f, apply fully_faithful_precomposition_naturality },
      { fapply nat_trans_eq, intro a, esimp,
        apply inverse,
        induction (fully_faithful_precomposition_functor_pair γ (to_fun_ob H a)) with g Hg =>
        esimp, apply concat, apply Hg a (iso.refl (H a)), esimp,
        apply concat, apply ap (fun x => x o _), apply respect_id, apply concat, apply id_left,
        apply concat, apply ap (fun x => _ o x), apply respect_id, apply id_right } }
Defined.

Defined. fully_faithful_precomposition

Defined. functor

namespace functor

  section essentially_surjective_precomposition

  parameters {A B : Precategory} {C : Category}
    {H : A ⇒ B} [He : is_weak_equivalence H] (F : A ⇒ C)
  variables {b b' : carrier B} (f : hom b b')
  include A B C H He F

  structure essentially_surj_precomp_X (b : carrier B) : Type.
    (c : carrier C)
    (k : forall (a : carrier A) (h : H a ≅ b), F a ≅ c)
    (k_coh : forall {a a'} h h' (f : hom a a'), to_hom h' o (to_fun_hom H f) = to_hom h
      -> to_hom (k a' h') o to_fun_hom F f = to_hom (k a h))
  local abbreviation X . essentially_surj_precomp_X
  local abbreviation X.mk . @essentially_surj_precomp_X.mk
  local abbreviation X.c . @essentially_surj_precomp_X.c
  local abbreviation X.k . @essentially_surj_precomp_X.k
  local abbreviation X.k_coh .  @essentially_surj_precomp_X.k_coh

  section
  variables {c c' : carrier C} (p : c = c')
    {k : forall (a : carrier A) (h : H a ≅ b), F a ≅ c}
    {k' : forall (a : carrier A) (h : H a ≅ b), F a ≅ c'}
    (q : forall (a : carrier A) (h : H a ≅ b), to_hom (k a h @i iso_of_eq p) = to_hom (k' a h))
    {k_coh : forall {a a'} h h' (f : hom a a'), to_hom h' o (to_fun_hom H f) = to_hom h
      -> to_hom (k a' h') o to_fun_hom F f = to_hom (k a h)}
    {k'_coh : forall {a a'} h h' (f : hom a a'), to_hom h' o (to_fun_hom H f) = to_hom h
      -> to_hom (k' a' h') o to_fun_hom F f = to_hom (k' a h)}
  include c c' p k k' q

  privateDefinition X_eq : X.mk c k @k_coh = X.mk c' k' @k'_coh.
Proof.
    cases p,
    assert q' : k = k',
    { apply eq_of_homotopy, intro a, apply eq_of_homotopy, intro h,
      apply iso_eq, apply !id_left^-1 @ q a h },
    cases q',
    apply ap (essentially_surj_precomp_X.mk c' k'),
    apply is_prop.elim
Defined.

Defined.

  open prod.ops sigma.ops
  privateDefinition X_prop [instance] : is_prop (X b).
Proof.
    induction He.2 b with Hb, cases Hb with a0 Ha0,
    fapply is_prop.mk, intros f g, cases f with cf kf kf_coh, cases g with cg kg kg_coh,
    fapply X_eq,
    { apply eq_of_iso, apply iso.trans, apply iso.symm, apply kf a0 Ha0,
      apply kg a0 Ha0 },
    { intro a h,
      assert fHf : Σ f : hom a a0, to_hom Ha0 o (to_fun_hom H f) = to_hom h =>
      { fconstructor, apply hom_inv, apply He.1, exact to_hom Ha0^-1ⁱ o to_hom h,
        apply concat, apply ap (fun x => _ o x), apply right_inv (to_fun_hom H) =>
        apply comp_inverse_cancel_left },
      apply concat, apply ap (fun x => to_hom x o _), apply iso_of_eq_eq_of_iso,
      apply concat, apply ap (fun x => _ o x), apply (kf_coh h Ha0 fHf.1 fHf.2)^-1,
      apply concat, rotate 1, apply kg_coh h Ha0 fHf.1 fHf.2,
      apply concat, apply assoc, apply ap (fun x => x o _),
      apply concat, apply !assoc^-1,
      apply concat, apply ap (fun x => _ o x), apply comp.left_inverse,
      apply id_right },
Defined.

  privateDefinition X_inh (b) : X b.
Proof.
    induction He.2 b with Hb, cases Hb with a0 Ha0,
    fconstructor, exact F a0,
    { intro a h, apply to_fun_iso F => apply reflect_iso H,
      exact h @i Ha0^-1ⁱ },
    { intros a a' h h' f HH,
      apply concat, apply !respect_comp^-1, apply ap (to_fun_hom F) =>
      esimp, rewrite [-HH],
      apply concat, apply ap (fun x => _ o x), apply inverse, apply left_inv (to_fun_hom H) =>
      apply concat, apply !hom_inv_respect_comp^-1, apply ap (hom_inv H),
      apply !assoc^-1 }
Defined.
  local abbreviation G0 . fun (b) => X.c (X_inh b)
  privateDefinition k . fun b => X.k (X_inh b)
  privateDefinition k_coh . fun b => @X.k_coh b (X_inh b)

  privateDefinition X_c_eq_of_eq {b} (t t' : X b) (p : t = t') : X.c t = X.c t'.
  by cases p; reflexivity

  privateDefinition X_k_eq_of_eq {b} (t t' : X b) (p : t = t') (a : carrier A) (h : H a ≅ b) :
    X_c_eq_of_eq t t' p # X.k t a h = X.k t' a h.
  by cases p; reflexivity

  privateDefinition X_phi {b} (t : X b) : X.c t = X.c (X_inh b).
  X_c_eq_of_eq _ _ !is_prop.elim

  privateDefinition X_phi_transp {b} (t : X b) (a : carrier A) (h : H a ≅ b) :
    (X_phi t) # (X.k t a h) = k b a h.
  by apply X_k_eq_of_eq t _ !is_prop.elim

  privateDefinition X_phi_hom_of_eq' {b} (t t' : X b) (p : t = t') (a : carrier A) (h : H a ≅ b) :
    X.k t' a h @i (iso_of_eq (X_c_eq_of_eq t t' p)^-1) = X.k t a h.
Proof.
    cases p, apply iso_eq, apply id_left
Defined.

  privateDefinition X_phi_hom_of_eq {b} (t : X b) (a : carrier A) (h : H a ≅ b) :
    to_hom (k b a h @i (iso_of_eq (X_phi t)^-1)) = to_hom (X.k t a h).
Proof.
    apply ap to_hom, apply X_phi_hom_of_eq'
Defined.

  structure essentially_surj_precomp_Y {b b' : carrier B} (f : hom b b') : Type.
    (g : hom (G0 b) (G0 b'))
    (Hg : forall {a a' : carrier A} h h' (l : hom a a'), to_hom h' o to_fun_hom H l = f o to_hom h ->
      to_hom (k b' a' h') o to_fun_hom F l = g o to_hom (k b a h))
  local abbreviation Y . @essentially_surj_precomp_Y
  local abbreviation Y.mk . @essentially_surj_precomp_Y.mk
  local abbreviation Y.g . @essentially_surj_precomp_Y.g

  section
  variables {g : hom (G0 b) (G0 b')} {g' : hom (G0 b) (G0 b')} (p : g = g')
    (Hg : forall {a a' : carrier A} h h' (l : hom a a'), to_hom h' o to_fun_hom H l = f o to_hom h ->
      to_hom (k b' a' h') o to_fun_hom F l = g o to_hom (k b a h))
    (Hg' : forall {a a' : carrier A} h h' (l : hom a a'), to_hom h' o to_fun_hom H l = f o to_hom h ->
      to_hom (k b' a' h') o to_fun_hom F l = g' o to_hom (k b a h))
  include p

  privateDefinition Y_eq : Y.mk g @Hg = Y.mk g' @Hg'.
Proof.
    cases p, apply ap (Y.mk g'),
    apply is_prop.elim,
Defined.

Defined.

  privateDefinition Y_prop [instance] : is_prop (Y f).
Proof.
    induction He.2 b with Hb, cases Hb with a0 h0,
    induction He.2 b' with Hb', cases Hb' with a0' h0',
    fapply is_prop.mk, intros,
    cases x with g0 Hg0, cases y with g1 Hg1,
    apply Y_eq,
    assert l0Hl0 : Σ l0 : hom a0 a0', to_hom h0' o to_fun_hom H l0 = f o to_hom h0 =>
    { fconstructor, apply hom_inv, apply He.1, exact to_hom h0'^-1ⁱ o f o to_hom h0,
      apply concat, apply ap (fun x => _ o x), apply right_inv (to_fun_hom H) =>
      apply comp_inverse_cancel_left },
    apply comp.cancel_right (to_hom (k b a0 h0)),
    apply concat, apply inverse, apply Hg0 h0 h0' l0Hl0.1 l0Hl0.2,
    apply Hg1 h0 h0' l0Hl0.1 l0Hl0.2
Defined.

  privateDefinition Y_inh : Y f.
Proof.
    induction He.2 b with Hb, cases Hb with a0 h0,
    induction He.2 b' with Hb', cases Hb' with a0' h0',
    assert l0Hl0 : Σ l0 : hom a0 a0', to_hom h0' o to_fun_hom H l0 = f o to_hom h0 =>
    { fconstructor, apply hom_inv, apply He.1, exact to_hom h0'^-1ⁱ o f o to_hom h0,
      apply concat, apply ap (fun x => _ o x), apply right_inv (to_fun_hom H) =>
      apply comp_inverse_cancel_left },
    fapply Y.mk,
    { refine to_hom (k b' a0' h0') o _ o to_hom (k b a0 h0)^-1ⁱ,
      apply to_fun_hom F => apply l0Hl0.1 },
    { intros a a' h h' l Hl, esimp, apply inverse,
      assert mHm : Σ m, to_hom h0 o to_fun_hom H m = to_hom h =>
      { fconstructor, apply hom_inv, apply He.1, exact to_hom h0^-1ⁱ o to_hom h,
        apply concat, apply ap (fun x => _ o x), apply right_inv (to_fun_hom H) =>
        apply comp_inverse_cancel_left },
      assert m'Hm' : Σ m', to_hom h0' o to_fun_hom H m' = to_hom h' =>
      { fconstructor, apply hom_inv, apply He.1, exact to_hom h0'^-1ⁱ o to_hom h',
        apply concat, apply ap (fun x => _ o x), apply right_inv (to_fun_hom H) =>
        apply comp_inverse_cancel_left },
      assert m'l0lm : l0Hl0.1 o mHm.1 = m'Hm'.1 o l,
      { apply faithful_of_fully_faithful, apply He.1,
        apply concat, apply respect_comp, apply comp.cancel_left (to_hom h0'), apply inverse,
        apply concat, apply ap (fun x => _ o x), apply respect_comp,
        apply concat, apply assoc,
        apply concat, apply ap (fun x => x o _), apply m'Hm'.2,
        apply concat, apply Hl,
        apply concat, apply ap (fun x => _ o x), apply mHm.2^-1,
        apply concat, apply assoc,
        apply concat, apply ap (fun x => x o _), apply l0Hl0.2^-1, apply !assoc^-1 },
      apply concat, apply !assoc^-1,
      apply concat, apply ap (fun x => _ o x), apply !assoc^-1,
      apply concat, apply ap (fun x => _ o _ o x), apply inverse_comp_eq_of_eq_comp,
       apply inverse, apply k_coh b h h0, apply mHm.2,
      apply concat, apply ap (fun x => _ o x), apply concat, apply !respect_comp^-1,
       apply concat, apply ap (to_fun_hom F) => apply m'l0lm, apply respect_comp,
      apply concat, apply assoc, apply ap (fun x => x o _),
      apply k_coh, apply m'Hm'.2 }
Defined.

  privateDefinition G_hom . fun {b b'} (f : hom b b') => Y.g (Y_inh f)
  privateDefinition G_hom_coh . fun {b b'} (f : hom b b') =>
    @essentially_surj_precomp_Y.Hg b b' f (Y_inh f)

  privateDefinition G_hom_id (b : carrier B) : G_hom (ID b) = ID (G0 b).
Proof.
    cases He with He1 He2, esimp[G_hom, Y_inh],
    induction He2 b with Hb, cases Hb with a h, --why do i need to destruct He?
    apply concat, apply ap (fun x => _ o x o _),
     apply concat, apply ap (to_fun_hom F) =>
      apply concat, apply ap (hom_inv H), apply inverse_comp_id_comp,
      apply hom_inv_respect_id,
     apply respect_id,
    apply comp_id_comp_inverse
Defined.

  privateDefinition G_hom_comp {b0 b1 b2 : carrier B} (g : hom b1 b2) (f : hom b0 b1) :
    G_hom (g o f) = G_hom g o G_hom f.
Proof.
    cases He with He1 He2, esimp[G_hom, Y_inh],
    induction He2 b0 with Hb0, cases Hb0 with a0 h0,
    induction He2 b1 with Hb1, cases Hb1 with a1 h1,
    induction He2 b2 with Hb2, cases Hb2 with b2 h2,
    apply concat, apply assoc,
    apply concat, rotate 1, apply !assoc^-1,
    apply concat, rotate 1, apply !assoc^-1,
    apply ap (fun x => x o _),
    apply inverse, apply concat, apply ap (fun x => x o _),
     apply concat, apply !assoc^-1, apply ap (fun x => _ o x),
     apply concat, apply !assoc^-1, apply ap (fun x => _ o x), apply comp.left_inverse,
    apply concat, apply !assoc^-1, apply ap (fun x => _ o x),
    apply concat, apply ap (fun x => x o _), apply id_right,
    apply concat, apply !respect_comp^-1, apply ap (to_fun_hom F) =>
    apply concat, apply !hom_inv_respect_comp^-1, apply ap (hom_inv H),
    apply concat, apply ap (fun x => x o _), apply assoc,
    apply concat, apply assoc,
    apply concat, apply ap (fun x => x o _), apply comp_inverse_cancel_right,
    apply concat, apply !assoc^-1, apply ap (fun x => _ o x),
    apply assoc,
Defined.

  privateDefinition G_functor : B ⇒ C.
Proof.
    fconstructor,
    { exact G0 },
    { intro b b' f, exact G_hom f },
    { intro b, apply G_hom_id },
    { intro a b c g f, apply G_hom_comp }
Defined.

  privateDefinition XF (a0 : carrier A) : X (H a0).
Proof.
    fconstructor,
    { exact F a0 },
    { intro a h, apply to_fun_iso F => apply reflect_iso, apply He.1, exact h },
    { intro a a' h h' f l, esimp,
      apply concat, apply !respect_comp^-1, apply ap (to_fun_hom F) => apply inverse,
      apply concat, apply ap (hom_inv H) l^-1,
      apply concat, apply hom_inv_respect_comp, apply ap (fun x => _ o x), apply left_inv }
Defined.

  privateDefinition G0_H_eq_F (a0 : carrier A) : G0 (H a0) = F a0.
Proof.
    apply inverse, apply X_phi (XF a0)
Defined.

  privateDefinition G_hom_H_eq_F {a0 a0' : carrier A} (f0 : hom a0 a0') :
    hom_of_eq (G0_H_eq_F a0') o G_hom (to_fun_hom H f0) o inv_of_eq (G0_H_eq_F a0)
    = to_fun_hom F f0.
Proof.
    apply comp_eq_of_eq_inverse_comp, apply comp_inverse_eq_of_eq_comp,
    apply concat, apply ap essentially_surj_precomp_Y.g, apply is_prop.elim,
    fconstructor,
    { exact (inv_of_eq (G0_H_eq_F a0') o to_fun_hom F f0) o hom_of_eq (G0_H_eq_F a0) } =>
    { intros a a' h h' l α, esimp[G0_H_eq_F], apply inverse,
      apply concat, apply !assoc^-1,
      apply concat, apply ap (fun x => _ o x), apply X_phi_hom_of_eq,
      apply concat, apply !assoc^-1,
      apply inverse_comp_eq_of_eq_comp, apply inverse,
      apply concat, apply assoc,
      apply concat, apply ap (fun x => x o _), apply X_phi_hom_of_eq, esimp[XF],
      refine !respect_comp^-1 @ ap (to_fun_hom F) _ @ !respect_comp =>
      apply eq_of_fn_eq_fn' (to_fun_hom H) =>
      refine !respect_comp @ _ @ !respect_comp^-1,
      apply concat, apply ap (fun x => x o _) !(right_inv (to_fun_hom H)) =>
      apply concat, rotate 1, apply ap (fun x => _ o x) !(right_inv (to_fun_hom H))^-1 =>
      exact α },
    reflexivity
Defined.

Defined. essentially_surjective_precomposition

Definition essentially_surjective_precomposition_functor [instance] {A B : Precategory}
    (C : Category) (H : A ⇒ B) [He : is_weak_equivalence H] :
    essentially_surjective (precomposition_functor C H).
Proof.
    intro F, apply tr, fconstructor, apply G_functor F =>
    apply iso_of_eq, fapply functor_eq =>
    { intro a, esimp[G_functor] => exact G0_H_eq_F F a },
    { intro a b f, exact G_hom_H_eq_F F f }
Defined.

  variables {C D E : Precategory}

Definition postcomposition_functor {C D} (E) (F : C ⇒ D)
    : C ^c E ⇒ D ^c E.
Proof.
    fapply functor.mk: esimp =>
    { intro G, exact F of G},
    { intro G H η, exact F ofn η},
    { intro G, apply fn_id},
    { intro G H I η θ, apply fn_n_distrib},
Defined.

Definition constant_diagram (C D) : C ⇒ C ^c D.
Proof.
    fapply functor.mk: esimp =>
    { intro c, exact constant_functor D c} =>
    { intro c d f, exact constant_nat_trans D f},
    { intro c, fapply nat_trans_eq, reflexivity},
    { intro c d e g f, fapply nat_trans_eq, reflexivity},
Defined.

Definition opposite_functor_opposite_left (C D : Precategory)
    : (C ^c D)ᵒᵖ ⇒ Cᵒᵖ ^c Dᵒᵖ.
Proof.
    fapply functor.mk: esimp =>
    { exact opposite_functor} =>
    { intro F G, exact opposite_nat_trans},
    { intro F, apply nat_trans_eq, reflexivity},
    { intro u v w g f, apply nat_trans_eq, reflexivity}
Defined.

Definition opposite_functor_opposite_right (C D : Precategory)
    : Cᵒᵖ ^c Dᵒᵖ ⇒ (C ^c D)ᵒᵖ.
Proof.
    fapply functor.mk: esimp =>
    { exact opposite_functor_rev} =>
    { apply @opposite_rev_nat_trans},
    { intro F, apply nat_trans_eq, intro d, reflexivity},
    { intro F G H η θ, apply nat_trans_eq, intro d, reflexivity}
Defined.

Definition constant_diagram_opposite (C D)
    : (constant_diagram C D)ᵒᵖᶠ = opposite_functor_opposite_right C D of constant_diagram Cᵒᵖ Dᵒᵖ.
Proof.
    fapply functor_eq =>
    { reflexivity },
    { intro c c' f, esimp at *, refine !nat_trans.id_right @ !nat_trans.id_left @ _,
      apply nat_trans_eq, intro d, reflexivity }
Defined.

Defined. functor
