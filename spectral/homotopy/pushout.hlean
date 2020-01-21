
import ..algebra.exactness homotopy.cofiber homotopy.wedge homotopy.smash

open eq function is_trunc sigma prod lift is_equiv equiv pointed sum unit bool cofiber

namespace pushout

  section
    variables {TL BL TR : pType} {f : TL ->* BL} {g : TL ->* TR}
              {TL' BL' TR' : pType} {f' : TL' ->* BL'} {g' : TL' ->* TR'}
              (tl : TL <~> TL') (bl : BL <~>* BL') (tr : TR <~> TR')
              (fh : bl o f == f' o tl) (gh : tr o g == g' o tl)

Definition ppushout_functor (tl : TL -> TL') (bl : BL ->* BL') (tr : TR -> TR')
      (fh : bl o f == f' o tl) (gh : tr o g == g' o tl) : ppushout f g ->* ppushout f' g' :=
    begin
      fconstructor,
      { exact pushout.functor tl bl tr fh gh } =>
      { exact ap inl (point_eq bl) },
    end

Definition ppushout_pequiv (tl : TL <~> TL') (bl : BL <~>* BL') (tr : TR <~> TR')
      (fh : bl o f == f' o tl) (gh : tr o g == g' o tl) : ppushout f g <~>* ppushout f' g' :=
    pequiv_of_equiv (pushout.equiv _ _ _ _ tl bl tr fh gh) (ap inl (point_eq bl))

Defined.

  (*
    WIP: proving that satisfying the universal property of the pushout is equivalent to
    being equivalent to the pushout
  *)

  universe variables u₁ u₂ u₃ u₄
  variables {A : Type.{u₁}} {B : Type.{u₂}} {C : Type.{u₃}} {D D' : Type.{u₄}}
            {f : A -> B} {g : A -> C} {h : B -> D} {k : C -> D} (p : h o f == k o g)
            {h' : B -> D'} {k' : C -> D'} (p' : h' o f == k' o g)

  include p
Definition is_pushout : Type :=
  forall (X : Type.{max u₁ u₂ u₃ u₄}) (h' : B -> X) (k' : C -> X) (p' : h' o f == k' o g),
    is_contr (Σ(l : D -> X) (v : l o h == h' \* l o k == k'),
                 forall a, square (prod.pr1 v (f a)) (prod.pr2 v (g a)) (ap l (p a)) (p' a))

Definition cocone (X : Type) : Type :=
  Σ(v : (B -> X) \* (C -> X)), prod.pr1 v o f == prod.pr2 v o g

Definition cocone_of_map (X : Type) (l : D -> X) : cocone p X :=
  ⟨(l o h, l o k), fun a => ap l (p a)⟩


  omit p

Definition is_pushout2 : Type :=
  forall (X : Type.{max u₁ u₂ u₃ u₄}), is_equiv (cocone_of_map p X)

  section
  open sigma.ops
  protectedDefinition inv_left (H : is_pushout2 p) {X : Type} (v : cocone p X) :
    (cocone_of_map p X)^-1ᶠ v o h == prod.pr1 v.1 :=
  ap10 (ap prod.pr1 (right_inv (cocone_of_map p X) v)..1)

  protectedDefinition inv_right (H : is_pushout2 p) {X : Type} (v : cocone p X) :
    (cocone_of_map p X)^-1ᶠ v o k == prod.pr2 v.1 :=
  ap10 (ap prod.pr2 (right_inv (cocone_of_map p X) v)..1)
Defined.

  section
    local attribute is_pushout [reducible]
Definition is_prop_is_pushout : is_prop (is_pushout p) :=
    _

    local attribute is_pushout2 [reducible]
Definition is_prop_is_pushout2 : is_prop (is_pushout2 p) :=
    _
Defined.

Definition ap_eq_apd10_ap {A B : Type} {C : B -> Type} (f : A -> forall b, C b) {a a' : A} (p : a = a') (b : B)
    : ap (fun a => f a b) p = apd10 (ap f p) b :=
  by induction p; reflexivity

  variables (f g)
Definition is_pushout2_pushout : @is_pushout2 _ _ _ _ f g inl inr glue :=
  fun X => to_is_equiv (pushout_arrow_equiv f g X @e assoc_equiv_prod _)

Definition is_equiv_of_is_pushout2_simple {A B C D : Type.{u₁}}
            {f : A -> B} {g : A -> C} {h : B -> D} {k : C -> D} (p : h o f == k o g)
            {h' : B -> D'} {k' : C -> D'} (p' : h' o f == k' o g)
 (H : is_pushout2 p) : D <~> pushout f g :=
Proof.
    fapply equiv.MK,
    { exact (cocone_of_map p _)^-1ᶠ ⟨(inl, inr), glue⟩ },
    { exact pushout.elim h k p },
    { intro x, exact sorry

},
    { apply ap10,
      apply inj (equiv.mk _ (H D)),
      fapply sigma_eq,
      { esimp, fapply prod_eq,
          apply eq_of_homotopy, intro b,
          exact ap (pushout.elim h k p) (pushout.inv_left p H ⟨(inl, inr), glue⟩ b),
          apply eq_of_homotopy, intro c,
          exact ap (pushout.elim h k p) (pushout.inv_right p H ⟨(inl, inr), glue⟩ c) },
      { apply pi.pi_pathover_constant, intro a,
        apply eq_pathover,
        refine !ap_eq_apd10_ap @ph _ @hp !ap_eq_apd10_ap^-1,
        refine ap (fun x => apd10 x _) (ap_compose (fun x => x o f) pr1 _ @ ap02 _ !prod_eq_pr1) @ph _
               @hp ap (fun x => apd10 x _) (ap_compose (fun x => x o g) pr2 _ @ ap02 _ !prod_eq_pr2)^-1,
        refine apd10 !apd10_ap_precompose_dependent a @ph _ @hp apd10 !apd10_ap_precompose_dependent^-1 a,
        refine !apd10_eq_of_homotopy @ph _ @hp !apd10_eq_of_homotopy^-1,
        refine ap_compose (pushout.elim h k p) _ _ @pv _,
        refine aps (pushout.elim h k p) _ @vp (!elim_glue @ !ap_id^-1),
        esimp,   exact sorry
        },
      }
Defined.






  (* composing pushouts *)

Definition pushout_vcompose_to {A B C D : Type} {f : A -> B} {g : A -> C} {h : B -> D}
    (x : pushout h (@inl _ _ _ f g)) : pushout (h o f) g :=
Proof.
    induction x with d y b,
    { exact inl d },
    { induction y with b c a,
      { exact inl (h b) },
      { exact inr c },
      { exact glue a }},
    { reflexivity }
Defined.

Definition pushout_vcompose_from {A B C D : Type} {f : A -> B} {g : A -> C} {h : B -> D}
    (x : pushout (h o f) g) : pushout h (@inl _ _ _ f g) :=
Proof.
    induction x with d c a,
    { exact inl d },
    { exact inr (inr c) },
    { exact glue (f a) @ ap inr (glue a) }
Defined.

Definition pushout_vcompose {A B C D : Type} (f : A -> B) (g : A -> C) (h : B -> D) :
    pushout h (@inl _ _ _ f g) <~> pushout (h o f) g :=
Proof.
    fapply equiv.MK,
    { exact pushout_vcompose_to },
    { exact pushout_vcompose_from },
    { intro x, induction x with d c a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose pushout_vcompose_to _ _ @ ap02 _ !elim_glue @ _,
        refine (ap_pp _ _ _) @ !elim_glue ◾ !ap_compose' @ (concat_1p _) @ _, esimp, apply elim_glue }},
    { intro x, induction x with d y b,
      { reflexivity },
      { induction y with b c a,
        { exact glue b },
        { reflexivity },
        { apply eq_pathover, refine ap_compose pushout_vcompose_from _ _ @ph _,
          esimp, refine ap02 _ !elim_glue @ !elim_glue @ph _, apply square_of_eq, reflexivity }},
      { apply eq_pathover_id_right, esimp,
        refine ap_compose pushout_vcompose_from _ _ @ ap02 _ !elim_glue @ph _, apply square_of_eq,
        reflexivity }}
Defined.

Definition pushout_hcompose {A B C D : Type} (f : A -> B) (g : A -> C) (h : C -> D) :
    pushout (@inr _ _ _ f g) h <~> pushout f (h o g) :=
  calc
    pushout (@inr _ _ _ f g) h <~> pushout h (@inr _ _ _ f g) : pushout.symm
      ... <~> pushout h (@inl _ _ _ g f) :
              pushout.equiv _ _ _ _ erfl erfl (pushout.symm f g) (fun a => idp) (fun a => idp)
      ... <~> pushout (h o g) f : pushout_vcompose
      ... <~> pushout f (h o g) : pushout.symm


Definition pushout_vcompose_equiv {A B C D E : Type} (f : A -> B) {g : A -> C} {h : B -> D}
    {hf : A -> D} {k : B -> E} (e : E <~> pushout f g) (p : k == e^-1ᵉ o inl) (q : h o f == hf) :
    pushout h k <~> pushout hf g :=
Proof.
    refine _ @e pushout_vcompose f g h @e _,
    { fapply pushout.equiv,
        reflexivity,
        reflexivity,
        exact e,
        reflexivity,
        exact homotopy_of_homotopy_inv_post e _ _ p },
    { fapply pushout.equiv,
        reflexivity,
        reflexivity,
        reflexivity,
        exact q,
        reflexivity },
Defined.

Definition pushout_hcompose_equiv {A B C D E : Type} {f : A -> B} (g : A -> C) {h : C -> E}
    {hg : A -> E} {k : C -> D} (e : D <~> pushout f g) (p : k == e^-1ᵉ o inr) (q : h o g == hg) :
    pushout k h <~> pushout f hg :=
  calc
    pushout k h <~> pushout h k : pushout.symm
      ... <~> pushout hg f : by exact pushout_vcompose_equiv _ (e @e pushout.symm f g) p q
      ... <~> pushout f hg : pushout.symm

Definition pushout_of_equiv_left_to {A B C : Type} {f : A <~> B} {g : A -> C}
    (x : pushout f g) : C :=
Proof.
    induction x with b c a,
    { exact g (f^-1 b) },
    { exact c },
    { exact ap g (left_inv f a) }
Defined.

Definition pushout_of_equiv_left {A B C : Type} (f : A <~> B) (g : A -> C) :
    pushout f g <~> C :=
Proof.
    fapply equiv.MK,
    { exact pushout_of_equiv_left_to },
    { exact inr },
    { intro c, reflexivity },
    { intro x, induction x with b c a,
      { exact (glue (f^-1 b))^-1 @ ap inl (right_inv f b) },
      { reflexivity },
      { apply eq_pathover_id_right, refine ap_compose inr _ _ @ ap02 _ !elim_glue @ph _,
        apply move_top_of_left, apply move_left_of_bot,
        refine ap02 _ (adj f _) @ !ap_compose^-1 @pv _ @vp !ap_compose,
        apply natural_square_tr }}
Defined.

Definition pushout_of_equiv_right {A B C : Type} (f : A -> B) (g : A <~> C) :
    pushout f g <~> B :=
  calc
    pushout f g <~> pushout g f : pushout.symm f g
            ... <~> B           : pushout_of_equiv_left g f

    variables {A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ : Type} {f₁ : A₁ -> B₁} {g₁ : A₁ -> C₁}
    {f₂ : A₂ -> B₂} {g₂ : A₂ -> C₂} {f₃ : A₃ -> B₃} {g₃ : A₃ -> C₃}
    {h₂ : A₂ -> A₃} {h₁ : A₁ -> A₂}
    {i₂ : B₂ -> B₃} {i₁ : B₁ -> B₂}
    {j₂ : C₂ -> C₃} {j₁ : C₁ -> C₂}
    (p₂ : i₂ o f₂ == f₃ o h₂) (q₂ : j₂ o g₂ == g₃ o h₂)
    (p₁ : i₁ o f₁ == f₂ o h₁) (q₁ : j₁ o g₁ == g₂ o h₁)

Definition pushout_functor_compose :
    pushout.functor (h₂ o h₁) (i₂ o i₁) (j₂ o j₁) (p₁ @htyv p₂) (q₁ @htyv q₂) ~
    pushout.functor h₂ i₂ j₂ p₂ q₂ o pushout.functor h₁ i₁ j₁ p₁ q₁ :=
Proof.
    intro x, induction x with b c a,
    { reflexivity },
    { reflexivity },
    { apply eq_pathover, apply hdeg_square, esimp,
      refine !elim_glue @ whisker_right _ ((ap_pp _ _ _) @ !ap_compose' ◾ idp) ◾
        (ap02 _ !con_inv @ (ap_pp _ _ _) @ whisker_left _ (ap02 _ !ap_inv^-1 @ !ap_compose')) @ _ @
        (ap_compose (pushout.functor h₂ i₂ j₂ p₂ q₂) _ _ @ ap02 _ !elim_glue)^-1 =>
      refine _ @ ((ap_pp _ _ _) @ ((ap_pp _ _ _) @ !ap_compose' ◾ !elim_glue) ◾ !ap_compose')^-1ᵖ,
      refine (concat_pp_p _ _ _)^-1 @ whisker_right _ _,
      exact whisker_right _ (concat_pp_p _ _ _) @ (concat_pp_p _ _ _) }
Defined.

  variables {p₁ q₁}
Definition pushout_functor_homotopy_constant {p₁' : i₁ o f₁ == f₂ o h₁} {q₁' : j₁ o g₁ == g₂ o h₁}
    (p : p₁ == p₁') (q : q₁ == q₁') :
    pushout.functor h₁ i₁ j₁ p₁ q₁ == pushout.functor h₁ i₁ j₁ p₁' q₁' :=
Proof.
    induction p, induction q, reflexivity
Defined.

Definition pushout_functor_homotopy {h₁ h₂ : A₁ -> A₂} {i₁ i₂ : B₁ -> B₂} {j₁ j₂ : C₁ -> C₂}
    {p₁ : i₁ o f₁ == f₂ o h₁} {q₁ : j₁ o g₁ == g₂ o h₁}
    {p₂ : i₂ o f₁ == f₂ o h₂} {q₂ : j₂ o g₁ == g₂ o h₂}
    (r : h₁ == h₂) (s : i₁ == i₂) (t : j₁ == j₂)
    (u : r @htyh p₁ == p₂ @htyh s) (v : r @htyh q₁ == q₂ @htyh t) :
    pushout.functor h₁ i₁ j₁ p₁ q₁ == pushout.functor h₂ i₂ j₂ p₂ q₂ :=
Proof.
    induction r, induction s, induction t, apply pushout_functor_homotopy_constant =>
    { exact (rfl_hhconcat p₁)^-1ʰᵗʸ @hty u @hty hhconcat_rfl p₂ },
    exact (rfl_hhconcat q₁)^-1ʰᵗʸ @hty v @hty hhconcat_rfl q₂
Defined.

  (* pushout where one map is constant is a cofiber *)

Definition pushout_const_equiv_to {A B C : Type} {f : A -> B} {c₀ : C}
    (x : pushout f (const A c₀)) : cofiber (sum_functor f (const unit c₀)) :=
Proof.
    induction x with b c a,
    { exact !cod (sum.inl b) },
    { exact !cod (sum.inr c) },
    { exact glue (sum.inl a) @ (glue (sum.inr ⋆))^-1 }
Defined.

Definition pushout_const_equiv_from {A B C : Type} {f : A -> B} {c₀ : C}
    (x : cofiber (sum_functor f (const unit c₀))) : pushout f (const A c₀) :=
Proof.
    induction x with v v,
    { induction v with b c, exact inl b, exact inr c },
    { exact inr c₀ },
    { induction v with a u, exact glue a, reflexivity }
Defined.

Definition pushout_const_equiv {A B C : Type} (f : A -> B) (c₀ : C) :
    pushout f (const A c₀) <~> cofiber (sum_functor f (const unit c₀)) :=
Proof.
    fapply equiv.MK,
    { exact pushout_const_equiv_to },
    { exact pushout_const_equiv_from },
    { intro x, induction x with v v,
      { induction v with b c, reflexivity, reflexivity },
      { exact glue (sum.inr ⋆) },
      { apply eq_pathover_id_right,
        refine ap_compose pushout_const_equiv_to _ _ @ ap02 _ !elim_glue @ph _,
        induction v with a u,
        { refine !elim_glue @ph _, apply whisker_bl, exact hrfl },
        { induction u, exact square_of_eq idp }}},
    { intro x, induction x with c b a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose pushout_const_equiv_from _ _ @ ap02 _ !elim_glue @ _,
        refine (ap_pp _ _ _) @ !elim_glue ◾ (!ap_inv @ !elim_glue⁻²) }}
Defined.

  (* wedge is the cofiber of the map 2 -> A + B *)

Definition sum_of_bool (A B : pType) (b : bool) : A + B :=
  by induction b; exact sum.inl (point _); exact sum.inr pt

Definition psum_of_pbool (A B : pType) : pbool ->* (A +* B) :=
  Build_pMap (sum_of_bool A B) idp

Definition wedge_equiv_pushout_sum (A B : pType) :
    wedge A B <~> cofiber (sum_of_bool A B) :=
Proof.
    refine pushout_const_equiv _ _ @e _,
    fapply pushout.equiv,
      exact bool_equiv_unit_sum_unit^-1ᵉ,
      reflexivity,
      reflexivity,
      intro x, induction x: reflexivity,
      intro x, induction x with u u: induction u; reflexivity
Defined.

  section
  open prod.ops
  (* products preserve pushouts *)

Definition pushout_prod_equiv_to {A B C D : Type} {f : A -> B} {g : A -> C}
    (xd : pushout f g \* D) : pushout (prod_functor f (@id D)) (prod_functor g id) :=
Proof.
    induction xd with x d, induction x with b c a,
    { exact inl (b, d) },
    { exact inr (c, d) },
    { exact glue (a, d) }
Defined.

Definition pushout_prod_equiv_from {A B C D : Type} {f : A -> B} {g : A -> C}
    (x : pushout (prod_functor f (@id D)) (prod_functor g id)) : pushout f g \* D :=
Proof.
    induction x with bd cd ad,
    { exact (inl bd.1, bd.2) },
    { exact (inr cd.1, cd.2) },
    { exact prod_eq (glue ad.1) idp }
Defined.

Definition pushout_prod_equiv {A B C D : Type} (f : A -> B) (g : A -> C) :
    pushout f g \* D <~> pushout (prod_functor f (@id D)) (prod_functor g id) :=
Proof.
    fapply equiv.MK,
    { exact pushout_prod_equiv_to },
    { exact pushout_prod_equiv_from },
    { intro x, induction x with bd cd ad,
      { induction bd, reflexivity },
      { induction cd, reflexivity },
      { induction ad with a d, apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose pushout_prod_equiv_to _ _ @ ap02 _ !elim_glue @ _, esimp,
        exact !ap_prod_elim @ (concat_1p _) @ !elim_glue }},
    { intro xd, induction xd with x d, induction x with b c a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        refine ap_compose (pushout_prod_equiv_from o pushout_prod_equiv_to) _ _ @ _,
        refine ap02 _ !ap_prod_mk_left @ !ap_compose @ _,
        refine ap02 _ (!ap_prod_elim @ (concat_1p _) @ !elim_glue) @ _,
        refine !elim_glue @ !ap_prod_mk_left^-1 }}
Defined.
Defined.

  (* interaction of pushout and sums *)

Definition pushout_to_sum {A B C : Type} {f : A -> B} {g : A -> C} (D : Type) (c₀ : C)
    (x : pushout f g) : pushout (sum_functor f (@id D)) (sum.rec g (fun d => c₀)) :=
Proof.
    induction x with b c a,
    { exact inl (sum.inl b) },
    { exact inr c },
    { exact glue (sum.inl a) }
Defined.

Definition pushout_from_sum {A B C : Type} {f : A -> B} {g : A -> C} (D : Type) (c₀ : C)
    (x : pushout (sum_functor f (@id D)) (sum.rec g (fun d => c₀))) : pushout f g :=
Proof.
    induction x with x c x,
    { induction x with b d, exact inl b, exact inr c₀ },
    { exact inr c },
    { induction x with a d, exact glue a, reflexivity }
Defined.

  (* The pushout of B <Definition pushout_sum_cancel_equiv {A B C : Type} (f : A -> B) (g : A -> C)
    (D : Type) (c₀ : C) : pushout f g <~> pushout (sum_functor f (@id D)) (sum.rec g (fun d => c₀)) :=
Proof.
    fapply equiv.MK,
    { exact pushout_to_sum D c₀ },
    { exact pushout_from_sum D c₀ },
    { intro x, induction x with x c x,
      { induction x with b d, reflexivity, esimp, exact (glue (sum.inr d))^-1 },
      { reflexivity },
      { apply eq_pathover_id_right,
        refine ap_compose (pushout_to_sum D c₀) _ _ @ ap02 _ !elim_glue @ph _,
        induction x with a d: esimp,
        { exact hdeg_square !elim_glue },
        { exact square_of_eq (con_Vp _) }}},
    { intro x, induction x with b c a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose (pushout_from_sum D c₀) _ _ @ ap02 _ !elim_glue @ !elim_glue }}
Defined.

Defined. pushout

namespace pushout

variables {A A' B B' C C' : Type} {f : A -> B} {g : A -> C} {f' : A' -> B'} {g' : A' -> C'}
Definition sum_pushout_of_pushout_sum [unfold 11]
  (x : pushout (sum_functor f f') (sum_functor g g')) : pushout f g ⊎ pushout f' g' :=
Proof.
  induction x with b c a,
  { exact sum_functor inl inl b } =>
  { exact sum_functor inr inr c } =>
  { induction a with a a', exact ap sum.inl (glue a), exact ap sum.inr (glue a') }
Defined.

Definition pushout_sum_of_sum_pushout [unfold 11]
  (x : pushout f g ⊎ pushout f' g') : pushout (sum_functor f f') (sum_functor g g') :=
Proof.
  induction x with x x,
  { exact pushout.functor sum.inl sum.inl sum.inl homotopy.rfl homotopy.rfl x } =>
  { exact pushout.functor sum.inr sum.inr sum.inr homotopy.rfl homotopy.rfl x }
Defined.

variables (f g f' g')
(*
  do we want to define this in terms of sigma_pushout? One possible disadvantage is that the
  computation on glue is less convenient
*)
Definition pushout_sum_equiv_sum_pushout :
  pushout (sum_functor f f') (sum_functor g g') <~> pushout f g ⊎ pushout f' g' :=
equiv.MK sum_pushout_of_pushout_sum pushout_sum_of_sum_pushout
  abstract begin
    intro x, induction x with x x,
    { induction x,
      { reflexivity },
      { reflexivity },
      apply eq_pathover, apply hdeg_square, esimp,
      exact ap_compose sum_pushout_of_pushout_sum _ _ @
        ap02 _ (!elim_glue @ (concat_p1 _) @ (concat_1p _)) @ !elim_glue },
    { induction x,
      { reflexivity },
      { reflexivity },
      apply eq_pathover, apply hdeg_square, esimp,
      exact ap_compose sum_pushout_of_pushout_sum _ _ @
        ap02 _ (!elim_glue @ (concat_p1 _) @ (concat_1p _)) @ !elim_glue },
Defined. end
  abstract begin
    intro x, induction x with b c a,
    { induction b: reflexivity },
    { induction c: reflexivity },
    { apply eq_pathover_id_right,
      refine ap_compose pushout_sum_of_sum_pushout _ _ @ ap02 _ !elim_glue @ph _,
      induction a with a a':
        (apply hdeg_square; refine !ap_compose' @ !elim_glue @ (concat_p1 _) @ (concat_1p _)) }
Defined. end

variables {f g f' g'}
variables {D E F D' E' F' : Type} {h : D -> E} {i : D -> F} {h' : D' -> E'} {i' : D' -> F'}
  {j : A -> D} {k : B -> E} {l : C -> F} {j' : A' -> D'} {k' : B' -> E'} {l' : C' -> F'}
  {j₂ : A' -> D} {k₂ : B' -> E} {l₂ : C' -> F}
  (s : hsquare f h j k) (t : hsquare g i j l)
  (s' : hsquare f' h' j' k') (t' : hsquare g' i' j' l')
  (s₂ : hsquare f' h j₂ k₂) (t₂ : hsquare g' i j₂ l₂)

Definition sum_rec_pushout_sum_equiv_sum_pushout :
  sum.rec (pushout.functor j k l s t) (pushout.functor j₂ k₂ l₂ s₂ t₂) o
  pushout_sum_equiv_sum_pushout f g f' g' ~
  pushout.functor (sum.rec j j₂) (sum.rec k k₂) (sum.rec l l₂)
                  (sum_rec_hsquare s s₂) (sum_rec_hsquare t t₂) :=
Proof.
  intro x, induction x with b c a,
  { induction b with b b': reflexivity },
  { induction c with c c': reflexivity },
  { exact abstract begin apply eq_pathover,
    refine !ap_compose @ ap02 _ !elim_glue @ph _,
    induction a with a a': exact hdeg_square (!ap_compose' @ !elim_glue @ !elim_glue^-1)
    end end }
Defined.

Definition pushout_sum_equiv_sum_pushout_natural :
  hsquare
    (pushout.functor (j +-> j') (k +-> k') (l +-> l')
                     (sum_functor_hsquare s s') (sum_functor_hsquare t t'))
    (pushout.functor j k l s t +-> pushout.functor j' k' l' s' t')
    (pushout_sum_equiv_sum_pushout f g f' g')
    (pushout_sum_equiv_sum_pushout h i h' i') :=
Proof.
  intro x, induction x with b c a,
  { induction b with b b': reflexivity },
  { induction c with c c': reflexivity },
  { exact abstract begin apply eq_pathover,
    refine !ap_compose @ ap02 _ !elim_glue @ph _ @hp (!ap_compose @ ap02 _ !elim_glue)^-1,
    refine (ap_pp _ _ _) @ ((ap_pp _ _ _) @ !ap_compose' ◾ !elim_glue) ◾ (!ap_compose' @ !ap_inv) @ph _,
    induction a with a a',
    { apply hdeg_square, refine !ap_compose' ◾ idp ◾ !ap_compose'⁻² @ _ @ !ap_compose'^-1,
      refine _ @ (ap_compose sum.inl _ _ @ ap02 _ !elim_glue)^-1,
      exact (ap_compose sum.inl _ _ ◾ idp @ (ap_pp _ _ _)^-1) ◾ (!ap_inv^-1 @ ap_compose sum.inl _ _) @
        (ap_pp _ _ _)^-1 },
    { apply hdeg_square, refine !ap_compose' ◾ idp ◾ !ap_compose'⁻² @ _ @ !ap_compose'^-1,
      refine _ @ (ap_compose sum.inr _ _ @ ap02 _ !elim_glue)^-1,
      exact (ap_compose sum.inr _ _ ◾ idp @ (ap_pp _ _ _)^-1) ◾ (!ap_inv^-1 @ ap_compose sum.inr _ _) @
        (ap_pp _ _ _)^-1 } end end }
Defined.

Defined. pushout

namespace pushout
open sigma sigma.ops
variables {X : Type} {A B C : X -> Type} {f : forall x, A x -> B x} {g : forall x, A x -> C x}
Definition sigma_pushout_of_pushout_sigma [unfold 7]
  (x : pushout (total f) (total g)) : Σx, pushout (f x) (g x) :=
Proof.
  induction x with b c a,
  { exact total (fun x => inl) b },
  { exact total (fun x => inr) c },
  { exact sigma_eq_right (glue a.2) }
Defined.

Definition pushout_sigma_of_sigma_pushout [unfold 7]
  (x : Σx, pushout (f x) (g x)) : pushout (total f) (total g) :=
pushout.functor (dpair x.1) (dpair x.1) (dpair x.1) homotopy.rfl homotopy.rfl x.2

variables (f g)
Definition pushout_sigma_equiv_sigma_pushout :
  pushout (total f) (total g) <~> Σx, pushout (f x) (g x) :=
equiv.MK sigma_pushout_of_pushout_sigma pushout_sigma_of_sigma_pushout
  abstract begin
    intro x, induction x with x y, induction y with b c a,
    { reflexivity },
    { reflexivity },
    { apply eq_pathover, apply hdeg_square, esimp,
      exact ap_compose sigma_pushout_of_pushout_sigma _ _ @
        ap02 _ (!elim_glue @ (concat_p1 _) @ (concat_1p _)) @ !elim_glue }
Defined. end
  abstract begin
    intro x, induction x with b c a,
    { induction b, reflexivity },
    { induction c, reflexivity },
    { apply eq_pathover_id_right,
      refine ap_compose pushout_sigma_of_sigma_pushout _ _ @ ap02 _ !elim_glue @ph _,
      induction a with a a',
        apply hdeg_square, refine !ap_compose' @ !elim_glue @ (concat_p1 _) @ (concat_1p _) }
Defined. end

variables {f g}
variables {X' : Type} {A' B' C' : X' -> Type} {f' : forall x, A' x -> B' x} {g' : forall x, A' x -> C' x}
  {s : X -> X'} {h₁ : forall x, A x -> A' (s x)} {h₂ : forall x, B x -> B' (s x)} {h₃ : forall x, C x -> C' (s x)}
  (p : forall x, h₂ x o f x == f' (s x) o h₁ x) (q : forall x, h₃ x o g x == g' (s x) o h₁ x)


Definition pushout_sigma_equiv_sigma_pushout_natural :
  hsquare
    (pushout.functor (sigma_functor s h₁) (sigma_functor s h₂) (sigma_functor s h₃)
      (fun a => sigma_eq_right (p a.1 a.2)) (fun a => sigma_eq_right (q a.1 a.2)))
    (sigma_functor s (fun x => pushout.functor (h₁ x) (h₂ x) (h₃ x) (p x) (q x)))
    (pushout_sigma_equiv_sigma_pushout f g) (pushout_sigma_equiv_sigma_pushout f' g') :=
Proof.
  intro x, induction x with b c a,
  { reflexivity },
  { reflexivity },
  { exact abstract begin apply eq_pathover, apply hdeg_square,
    refine !ap_compose @ ap02 _ !elim_glue @ (ap_pp _ _ _) @
      ((ap_pp _ _ _) @ (!ap_compose' @ !ap_compose') ◾ !elim_glue) ◾
      (!ap_compose' @ ap02 _ !ap_inv^-1 @ !ap_compose') @ _,
    symmetry,
    refine
      ap_compose (sigma_functor s (fun x => pushout.functor (h₁ x) (h₂ x) (h₃ x) (p x) (q x))) _ _ @
      ap02 _ !elim_glue @ !ap_compose' @ ap_compose (dpair _) _ _ @ _,
    exact ap02 _ !elim_glue @ (ap_pp _ _ _) @ ((ap_pp _ _ _) @ !ap_compose' ◾ idp) ◾ !ap_compose'
Defined. end }
Defined.


  (* an induction principle for the cofiber of f : A -> B if A is a pushout where the second map has a section.
     The Pgluer is modified to get the right coherence
     See https://github.com/HoTT/HoTT-Agda/blob/master/Definitions/homotopy/elims/CofPushoutSection.agda
  *)

  open sigma.ops
Definition cofiber_pushout_helper' {A : Type} {B : A -> Type} {a₀₀ a₀₂ a₂₀ a₂₂ : A} {p₀₁ : a₀₀ = a₀₂}
    {p₁₀ : a₀₀ = a₂₀} {p₂₁ : a₂₀ = a₂₂} {p₁₂ : a₀₂ = a₂₂} {s : square p₀₁ p₂₁ p₁₀ p₁₂}
    {b₀₀ : B a₀₀} {b₂₀ : B a₂₀} {b₀₂ : B a₀₂} {b₂₂ b₂₂' : B a₂₂} {q₁₀ : b₀₀ =[p₁₀] b₂₀}
    {q₀₁ : b₀₀ =[p₀₁] b₀₂} {q₂₁ : b₂₀ =[p₂₁] b₂₂'} {q₁₂ : b₀₂ =[p₁₂] b₂₂} :
    Σ(r : b₂₂' = b₂₂), squareover B s q₀₁ (r # q₂₁) q₁₀ q₁₂ :=
Proof.
    induction s,
    induction q₀₁ using idp_rec_on,
    induction q₂₁ using idp_rec_on,
    induction q₁₀ using idp_rec_on,
    induction q₁₂ using idp_rec_on,
    exact ⟨idp, idso⟩
Defined.

Definition cofiber_pushout_helper {A B C D : Type} {f : A -> B} {g : A -> C} {h : pushout f g -> D}
    {P : cofiber h -> Type} {Pcod : forall d, P (cofiber.cod h d)} {Pbase : P (cofiber.base h)}
    (Pgluel : forall (b : B), Pcod (h (inl b)) =[cofiber.glue (inl b)] Pbase)
    (Pgluer : forall (c : C), Pcod (h (inr c)) =[cofiber.glue (inr c)] Pbase)
    (a : A) : Σ(p : Pbase = Pbase), squareover P (natural_square cofiber.glue (glue a))
      (Pgluel (f a)) (p # Pgluer (g a))
      (pathover_ap P (fun a => cofiber.cod h (h a)) (apd (fun a => Pcod (h a)) (glue a)))
      (pathover_ap P (fun a => cofiber.base h) (apd (fun a => Pbase) (glue a))) :=
  !cofiber_pushout_helper'

Definition cofiber_pushout_rec {A B C D : Type} {f : A -> B} {g : A -> C} {h : pushout f g -> D}
    {P : cofiber h -> Type} (Pcod : forall d, P (cofiber.cod h d)) (Pbase : P (cofiber.base h))
    (Pgluel : forall (b : B), Pcod (h (inl b)) =[cofiber.glue (inl b)] Pbase)
    (Pgluer : forall (c : C), Pcod (h (inr c)) =[cofiber.glue (inr c)] Pbase)
    (r : C -> A) (p : forall a, r (g a) = a)
    (x : cofiber h) : P x :=
Proof.
    induction x with d x,
    { exact Pcod d },
    { exact Pbase },
    { induction x with b c a,
      { exact Pgluel b },
      { exact (cofiber_pushout_helper Pgluel Pgluer (r c)).1 # Pgluer c },
      { apply pathover_pathover, rewrite [p a], exact (cofiber_pushout_helper Pgluel Pgluer a).2 }}
Defined.

  (* universal property of cofiber *)

Definition cofiber_exact_1 {X Y Z : pType} (f : X ->* Y) (g : pcofiber f ->* Z) :
    (g o* pcod f) o* f ==* pconst X Z :=
  !passoc @* pwhisker_left _ !pcod_pcompose @* !pcompose_pconst

  protectedDefinition pcofiber.elim {X Y Z : pType} {f : X ->* Y} (g : Y ->* Z)
    (p : g o* f ==* pconst X Z) : pcofiber f ->* Z :=
Proof.
    fapply Build_pMap,
    { intro w, induction w with y x, exact g y, exact (point _), exact p x },
    { reflexivity }
Defined.

  protectedDefinition pcofiber.elim_pcod {X Y Z : pType} {f : X ->* Y} {g : Y ->* Z}
    (p : g o* f ==* pconst X Z) : pcofiber.elim g p o* pcod f ==* g :=
Proof.
    fapply Build_pHomotopy,
    { intro y, reflexivity },
    { esimp, refine (concat_1p _) @ _,
      refine _ @ ((ap_pp _ _ _) @ (!ap_compose' @ !ap_inv) ◾ !elim_glue)^-1,
      apply eq_inv_con_of_con_eq, exact (point_htpy p)^-1 }
Defined.

Definition pcofiber_elim_unique {X Y Z : pType} {f : X ->* Y}
    {g₁ g₂ : pcofiber f ->* Z} (h : g₁ o* pcod f ==* g₂ o* pcod f)
    (sq : forall x, square (h (f x)) (point_eq g₁ @ (point_eq g₂)^-1)
      (ap g₁ (cofiber.glue x)) (ap g₂ (cofiber.glue x))) : g₁ ==* g₂ :=
Proof.
    fapply Build_pHomotopy,
    { intro x, induction x with y x,
      { exact h y },
      { exact point_eq g₁ @ (point_eq g₂)^-1 },
      { apply eq_pathover, exact sq x }},
    { apply inv_con_cancel_right }
Defined.

  (*
    The maps  Z^{C_f} --> Z^Y --> Z^X  are exact at Z^Y.
    Here Y^X means pointed maps from X to Y and C_f is the cofiber of f.
    The maps are given by precomposing with (pcod f) and f.
  *)
Definition cofiber_exact {X Y Z : pType} (f : X ->* Y) :
    is_exact_t (@ppcompose_right _ _ Z (pcod f)) (ppcompose_right f) :=
Proof.
    constructor,
    { intro g, apply path_pforall, apply cofiber_exact_1 },
    { intro g p, note q := phomotopy_path p,
      exact fiber.mk (pcofiber.elim g q) (path_pforall (pcofiber.elim_pcod q)) }
Defined.

  (* cofiber of pcod is suspension *)

Definition pcofiber_pcod {A B : pType} (f : A ->* B) : pcofiber (pcod f) <~>* susp A :=
Proof.
    fapply pequiv_of_equiv,
    { refine !pushout.symm @e _,
      exact pushout_vcompose_equiv f equiv.rfl homotopy.rfl homotopy.rfl },
    reflexivity
Defined.



Defined. pushout

namespace pushout
  (* define the quotient using pushout *)
  section
  open quotient sigma.ops
  variables {A B : Type} (R : A -> A -> Type) {Q : B -> B -> Type}
    (f : A -> B) (k : forall a a' : A, R a a' -> Q (f a) (f a'))

Definition pushout_quotient {A : Type} (R : A -> A -> Type) : Type :=
  @pushout ((Σa a', R a a') ⊎ (Σa a', R a a')) A (Σa a', R a a')
     (sum.rec pr1 (fun x => x.2.1)) (sum.rec id id)

  variable {R}
Definition pushout_quotient_of_quotient (x : quotient R) : pushout_quotient R :=
Proof.
    induction x with a a a' r,
    { exact inl a },
    { exact glue (sum.inl ⟨a, a', r⟩) @ (glue (sum.inr ⟨a, a', r⟩))^-1 }
Defined.

Definition quotient_of_pushout_quotient (x : pushout_quotient R) : quotient R :=
Proof.
    induction x with a x x,
    { exact class_of R a },
    { exact class_of R x.2.1 },
    { induction x with x x, exact eq_of_rel R x.2.2, reflexivity }
Defined.

  variable (R)
Definition quotient_equiv_pushout : quotient R <~> pushout_quotient R :=
  equiv.MK pushout_quotient_of_quotient quotient_of_pushout_quotient
    abstract begin
      intro x, induction x with a x x,
      { reflexivity },
      { exact glue (sum.inr x) },
      { apply eq_pathover_id_right,
        refine ap_compose pushout_quotient_of_quotient _ _ @ ap02 _ !elim_glue @ph _,
        induction x with x x,
        { refine !elim_eq_of_rel @ph _, induction x with a x, induction x with a' r,
          exact whisker_bl _ hrfl },
        { exact square_of_eq idp }}
    end end
    abstract begin
      intro x, induction x,
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose quotient_of_pushout_quotient _ _ @ ap02 _ !elim_eq_of_rel @ _,
        exact (ap_pp _ _ _) @ !elim_glue ◾ (!ap_inv @ !elim_glue⁻²) }
    end end

  variable {R}
Definition sigma_functor2 : (Σ a a' => R a a') -> (Σ b b', Q b b') :=
  sigma_functor f (fun a => sigma_functor f (k a))

Definition pushout_quotient_functor : pushout_quotient R -> pushout_quotient Q :=
  let tf := sigma_functor2 f k in
  pushout.functor (sum_functor tf tf) f tf
    begin intro x, induction x: reflexivity end begin intro x, induction x: reflexivity end

Definition quotient_equiv_pushout_natural :
    hsquare (quotient.functor f k) (pushout_quotient_functor f k)
      (quotient_equiv_pushout R) (quotient_equiv_pushout Q) :=
Proof.
    intro x, induction x with a a a' r,
    { reflexivity },
    { apply eq_pathover, apply hdeg_square,
      refine ap_compose pushout_quotient_of_quotient _ _ @ _ @
        (ap_compose (pushout.functor _ _ _ _ _) _ _)^-1 =>
      refine ap02 _ !elim_eq_of_rel @ _ @ (ap02 _ !elim_eq_of_rel)^-1,
      refine !elim_eq_of_rel @ _,
      exact ((ap_pp _ _ _) @ (!pushout.elim_glue @ (concat_p1 _) @ (concat_1p _)) ◾
             (!ap_inv @ (!pushout.elim_glue @ (concat_p1 _) @ (concat_1p _))⁻²))^-1 }
Defined.


Defined.

  variables {A B : pType}
  open smash

Definition prod_of_wedge (v : wedge A B) : A \* B :=
Proof.
    induction v with a b ,
    { exact (a, (point _)) },
    { exact ((point _), b) },
    { reflexivity }
Defined.

Definition wedge_of_sum (v : A + B) : wedge A B :=
Proof.
    induction v with a b,
    { exact pushout.inl a },
    { exact pushout.inr b }
Defined.

Definition prod_of_wedge_of_sum (v : A + B) :
    prod_of_wedge (wedge_of_sum v) = prod_of_sum v :=
Proof.
    induction v with a b,
    { reflexivity },
    { reflexivity }
Defined.

Definition eq_inl_pushout_wedge_of_sum (v : wedge A B) :
    inl (point _) = inl v :> pushout wedge_of_sum bool_of_sum :=
Proof.
    induction v with a b,
    { exact glue (sum.inl (point _)) @ (glue (sum.inl a))^-1, },
    { exact ap inl (glue ⋆) @ glue (sum.inr (point _)) @ (glue (sum.inr b))^-1, },
    { apply eq_pathover_constant_left,
      refine (con_pV _) @pv _ @vp !con_inv_cancel_right^-1, exact square_of_eq idp }
Defined.

  variables (A B)
Definition eq_inr_pushout_wedge_of_sum (b : bool) :
    inl (point _) = inr b :> pushout (@wedge_of_sum A B) bool_of_sum :=
Proof.
    induction b,
    { exact glue (sum.inl (point _)) },
    { exact ap inl (glue ⋆) @ glue (sum.inr (point _)) }
Defined.

Definition is_contr_pushout_wedge_of_sum : is_contr (pushout (@wedge_of_sum A B) bool_of_sum) :=
Proof.
    apply is_contr.mk (pushout.inl (point _)),
    intro x, induction x with v b w,
    { apply eq_inl_pushout_wedge_of_sum },
    { apply eq_inr_pushout_wedge_of_sum },
    { apply eq_pathover_constant_left_id_right,
      induction w with a b,
      { apply whisker_rt, exact vrfl },
      { apply whisker_rt, exact vrfl }}
Defined.

Definition bool_of_sum_of_bool {A B : pType} (b : bool) : bool_of_sum (sum_of_bool A B b) = b :=
  by induction b: reflexivity

  (* a different proof, using pushout lemmas, and the fact that the wedge is the pushout of
     A + B <Definition pushout_wedge_of_sum_equiv_unit : pushout (@wedge_of_sum A B) bool_of_sum <~> unit :=
Proof.
    refine pushout_hcompose_equiv (sum_of_bool A B) (wedge_equiv_pushout_sum A B @e !pushout.symm)
             _ _ @e _,
      exact erfl,
      intro x, induction x,
      reflexivity, reflexivity,
      exact bool_of_sum_of_bool,
    apply pushout_of_equiv_right
Defined.

Defined. pushout

namespace pushout   (* the wedge connectivity lemma actually works as intended *)
  section
  open trunc_index is_conn prod prod.ops

      privateDefinition tricky_lemma {A B : Type} (f : A -> B) {a a' : A}
    (p : a = a') (P : B -> Type) {r : f a = f a'} (α : ap f p = r)
    (s : forall x, P (f x)) (e : forall y, P y)
    (q : e (f a) = s a) (q' : e (f a') = s a')
    (H : (ap (transport P r) q)^-1 @ (apdt e r @ q')
         = (tr_compose P f p (s a) @ ap (fun u => transport P u (s a)) α)^-1 @ apdt s p)
    : q =[p] q' :=
Proof.
    induction α, induction p, apply pathover_idp_of_eq, esimp, esimp at H,
    rewrite ap_id at H, rewrite idp_con at H,
    exact (eq_con_of_inv_con_eq H)^-1,
Defined.

  parameters (n m : ℕ) {A B : pType}

  privateDefinition section_of_glue (P : A \* B -> Type)
    (s : forall w, P (prod_of_wedge w))
    : (s (inl (point _))  = s (inr (point _)) :> P ((point _), (point _))) :=
  ((tr_compose P prod_of_wedge (glue star) (s (inl (point _))))
    @ (ap (fun q => transport P q (s (inl (point _))))
    (wedge.elim_glue (fun a => (a, (point _))) (fun b => ((point _), b)) idp)))^-1 @ (apdt s (glue star))

  parameters (A B)
  parameters [cA : is_conn n A] [cB : is_conn m B]
  include cA cB

Definition is_conn_fun_prod_of_wedge : is_conn_fun (m + n) (@prod_of_wedge A B) :=
Proof.
    apply is_conn.is_conn_fun.intro => intro P, fapply is_retraction.mk,
    { intros s z, induction z with a b,
      exact @wedge_extension.ext A B n m cA cB (fun a b => P (a, b))
        (fun a b => transport (fun k => is_trunc k (P (a, b))) (of_nat_add_of_nat m n)
          (trunctype.struct (P (a, b))))
        (fun a => s (inl a)) (fun b => s (inr b))
        (section_of_glue P s) a b },
    { intro s, apply eq_of_homotopy, intro w, induction w with a b,
      { esimp, apply wedge_extension.β_left },
      { esimp, apply wedge_extension.β_right },
      { esimp, apply @tricky_lemma (wedge A B) (A \* B)
          (@prod_of_wedge A B) (inl (point _)) (inr (point _)) wedge.glue P idp
          (wedge.elim_glue (fun a => (a, (point _))) (fun b => ((point _), b)) idp) s
          (prod.rec (@wedge_extension.ext A B n m cA cB (fun a b => P (a, b))
            (fun a b => transport (fun k => is_trunc k (P (a, b))) (of_nat_add_of_nat m n)
              (trunctype.struct (P (a, b))))
              (fun a => s (inl a)) (fun b => s (inr b)) (section_of_glue P s))),
        esimp, rewrite [ap_id,idp_con], apply wedge_extension.coh } }
Defined.

Defined.
Defined. pushout

namespace pushout
  (* alternative version of the flattening lemma *)
    section
  open sigma sigma.ops

  universe variables u₁ u₂ u₃ u₄
  parameters {TL : Type.{u₁}} {BL : Type.{u₂}} {TR : Type.{u₃}}
             (f : TL -> BL) (g : TL -> TR) (P : pushout f g -> Type.{u₄})

  local abbreviation F : sigma (fun x => P (inl (f x))) -> sigma (P o inl) :=
  fun z => ⟨ f z.1 , z.2 ⟩

  local abbreviation G : sigma (fun x => P (inl (f x))) -> sigma (P o inr) :=
  fun z => ⟨ g z.1 , transport P (glue z.1) z.2 ⟩

  local abbreviation Pglue : forall x, P (inl (f x)) <~> P (inr (g x)) :=
  fun x => equiv.mk (transport P (glue x)) (is_equiv_tr P (glue x))

  protectedDefinition flattening' : sigma P <~> pushout F G :=
Proof.
    assert H : forall w, P w <~> pushout.elim_type (P o inl) (P o inr) Pglue w,
    { intro w, induction w with x x x,
      { exact erfl }, { exact erfl },
      { apply equiv_pathover2, intro pfx pgx q,
        apply pathover_of_tr_eq,
        apply eq.trans (ap10 (elim_type_glue.{u₁ u₂ u₃ u₄}
          (P o inl) (P o inr) Pglue x) pfx),         exact tr_eq_of_pathover q } },
    apply equiv.trans (sigma_equiv_sigma_right H),
    exact pushout.flattening f g (P o inl) (P o inr) Pglue
Defined.

Defined.
Defined. pushout
