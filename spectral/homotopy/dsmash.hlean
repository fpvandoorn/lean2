
(*

The "dependent" smash product.

Given A : pType and B : A -> pType it is the cofiber of
A ∨ B (point _) -> Σ(a : A), B a
However, we define it (equivalently) as the pushout of 2 ← A + B (point _) -> Σ(a : A), B a.
*)

import .smash_adjoint ..pointed_binary

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber sigma.ops wedge sigma function prod.ops

namespace dsmash

  variables {A : pType} {B : A -> pType}

Definition sigma_of_sum (u : A + B (point _)) : Σa, B a.
  by induction u with a b; exact ⟨a, (point _)⟩; exact ⟨(point _), b⟩

Definition dsmash' (B : A -> pType) : Type . pushout.pushout (@sigma_of_sum A B) (@smash.bool_of_sum A (B (point _)))
  protectedDefinition mk' (a : A) (b : B a) : dsmash' B . pushout.inl ⟨a, b⟩

Definition dsmash (B : A -> pType) : pType.
  pointed.MK (dsmash' B) (dsmash.mk' (point _) pt)

  notation `⋀` . dsmash

  protectedDefinition mk (a : A) (b : B a) : ⋀ B . pushout.inl ⟨a, b⟩
Definition auxl : ⋀ B . pushout.inr ff
Definition auxr : ⋀ B . pushout.inr tt
Definition gluel (a : A) : dsmash.mk a (point _) = auxl :> ⋀ B . pushout.glue (sum.inl a)
Definition gluer (b : B (point _)) : dsmash.mk (point _) b = auxr :> ⋀ B . pushout.glue (sum.inr b)

Definition gluel' (a a' : A) : dsmash.mk a (point _) = dsmash.mk a' (point _) :> ⋀ B.
  gluel a @ (gluel a')^-1
Definition gluer' (b b' : B (point _)) : dsmash.mk (point _) b = dsmash.mk (point _) b' :> ⋀ B.
  gluer b @ (gluer b')^-1
Definition glue (a : A) (b : B (point _)) : dsmash.mk a (point _) = dsmash.mk (point _) b :> ⋀ B.
  gluel' a (point _) @ gluer' (point _) b

Definition glue_pt_left (b : B (point _)) : glue (Point A) b = gluer' (point _) b.
  whisker_right _ (con_pV _) @ (concat_1p _)

Definition glue_pt_right (a : A) : glue a (Point (B a)) = gluel' a (point _).
  proof whisker_left _ (con_pV _) qed

Definition ap_mk_left {a a' : A} (p : a = a') : ap (fun a => dsmash.mk a (Point (B a))) p = gluel' a a'.
  !ap_is_constant

Definition ap_mk_right {b b' : B (point _)} (p : b = b') : ap (dsmash.mk (Point A)) p = gluer' b b'.
  !ap_is_constant

  protectedDefinition rec {P : ⋀ B -> Type} (Pmk : forall a b, P (dsmash.mk a b))
  (Pl : P auxl) (Pr : P auxr) (Pgl : forall a, Pmk a (point _) =[gluel a] Pl)
  (Pgr : forall b, Pmk (point _) b =[gluer b] Pr) (x : dsmash' B) : P x.
Proof.
  induction x with x b u,
  { induction x with a b, exact Pmk a b },
  { induction b, exact Pl, exact Pr },
  { induction u,
  { apply Pgl },
  { apply Pgr }}
Defined.

Definition rec_gluel {P : ⋀ B -> Type} {Pmk : forall a b, P (dsmash.mk a b)}
  {Pl : P auxl} {Pr : P auxr} (Pgl : forall a, Pmk a (point _) =[gluel a] Pl)
  (Pgr : forall b, Pmk (point _) b =[gluer b] Pr) (a : A) :
  apd (dsmash.rec Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a.
  !pushout.rec_glue

Definition rec_gluer {P : ⋀ B -> Type} {Pmk : forall a b, P (dsmash.mk a b)}
  {Pl : P auxl} {Pr : P auxr} (Pgl : forall a, Pmk a (point _) =[gluel a] Pl)
  (Pgr : forall b, Pmk (point _) b =[gluer b] Pr) (b : B (point _)) :
  apd (dsmash.rec Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b.
  !pushout.rec_glue

Definition rec_glue {P : ⋀ B -> Type} {Pmk : forall a b, P (dsmash.mk a b)}
  {Pl : P auxl} {Pr : P auxr} (Pgl : forall a, Pmk a (point _) =[gluel a] Pl)
  (Pgr : forall (b : B (point _)), Pmk (point _) b =[gluer b] Pr) (a : A) (b : B (point _)) :
  apd (dsmash.rec Pmk Pl Pr Pgl Pgr) (dsmash.glue a b) =
  (Pgl a @o (Pgl (point _))^-1ᵒ) @o (Pgr (point _) @o (Pgr b)^-1ᵒ).
  by rewrite [↑glue, ↑gluel', ↑gluer', +apd_con, +apd_inv, +rec_gluel, +rec_gluer]

  protectedDefinition elim {P : Type} (Pmk : forall a b, P) (Pl Pr : P)
  (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B (point _), Pmk (point _) b = Pr) (x : dsmash' B) : P.
  dsmash.rec Pmk Pl Pr (fun a => pathover_of_eq _ (Pgl a)) (fun b => pathover_of_eq _ (Pgr b)) x

  protectedDefinition elim' {P : Type} (Pmk : forall a b, P)
  (Pgl : forall a : A, Pmk a (point _) = Pmk (point _) pt) (Pgr : forall b : B (point _), Pmk (point _) b = Pmk (point _) pt)
  (ql : Pgl (point _) = idp) (qr : Pgr (point _) = idp) (x : dsmash' B) : P.
  dsmash.elim Pmk (Pmk (point _) pt) (Pmk (point _) pt) Pgl Pgr x

Definition elim_gluel {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
  (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B (point _), Pmk (point _) b = Pr) (a : A) :
  ap (dsmash.elim Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a.
Proof.
  apply inj_inv !(pathover_constant (@gluel A B a)),
  rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑dsmash.elim,rec_gluel],
Defined.

Definition elim_gluer {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
  (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B (point _), Pmk (point _) b = Pr) (b : B (point _)) :
  ap (dsmash.elim Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b.
Proof.
  apply inj_inv !(pathover_constant (@gluer A B b)),
  rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑dsmash.elim,rec_gluer],
Defined.

Definition elim_glue {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
  (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B (point _), Pmk (point _) b = Pr) (a : A) (b : B (point _)) :
  ap (dsmash.elim Pmk Pl Pr Pgl Pgr) (glue a b) = (Pgl a @ (Pgl (point _))^-1) @ (Pgr (point _) @ (Pgr b)^-1).
  by rewrite [↑glue, ↑gluel', ↑gluer', +ap_con, +ap_inv, +elim_gluel, +elim_gluer]

Defined. dsmash
open dsmash



namespace dsmash

  variables {A A' C : pType} {B : A -> pType} {D : C -> pType} {a a' : A} {b : B a} {b' : B a'}

Definition mk_eq_mk (p : a = a') (q : b =[p] b') : dsmash.mk a b = dsmash.mk a' b'.
  ap pushout.inl (dpair_eq_dpair p q)

Definition gluer2 (b : B a) (p : a = (point _)) : dsmash.mk a b = auxr.
  mk_eq_mk p !pathover_tr @ gluer _

Definition elim_gluel' {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
  (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B (point _), Pmk (point _) b = Pr) (a a' : A) :
  ap (dsmash.elim Pmk Pl Pr Pgl Pgr) (gluel' a a') = Pgl a @ (Pgl a')^-1.
  (ap_pp _ _ _) @ whisker_left _ !ap_inv @ !elim_gluel ◾ !elim_gluel⁻²

Definition elim_gluer' {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
  (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B (point _), Pmk (point _) b = Pr) (b b' : B (point _)) :
  ap (dsmash.elim Pmk Pl Pr Pgl Pgr) (gluer' b b') = Pgr b @ (Pgr b')^-1.
  (ap_pp _ _ _) @ whisker_left _ !ap_inv @ !elim_gluer ◾ !elim_gluer⁻²

Definition elim_gluel'_same {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
  (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B (point _), Pmk (point _) b = Pr) (a : A) :
  elim_gluel' Pgl Pgr a a =
  ap02 (dsmash.elim Pmk Pl Pr Pgl Pgr) (con.right_inv (gluel a)) @ (con.right_inv (Pgl a))^-1.
Proof.
  refine _ @ whisker_right _ (eq_top_of_square ((ap_pp _ _ _)_right_inv_sq))^-1,
  refine _ @ whisker_right _ (concat_p1 _)^-1,
  refine _ @ (concat_pp_p _ _ _)^-1,
  apply whisker_left,
  apply eq_con_inv_of_con_eq, symmetry,
  apply con_right_inv_natural
Defined.

Definition elim_gluer'_same {P : Type} {Pmk : forall a b, P} {Pl Pr : P}
  (Pgl : forall a : A, Pmk a (point _) = Pl) (Pgr : forall b : B (point _), Pmk (point _) b = Pr) (b : B (point _)) :
  elim_gluer' Pgl Pgr b b =
  ap02 (dsmash.elim Pmk Pl Pr Pgl Pgr) (con.right_inv (gluer b)) @ (con.right_inv (Pgr b))^-1.
Proof.
  refine _ @ whisker_right _ (eq_top_of_square ((ap_pp _ _ _)_right_inv_sq))^-1,
  refine _ @ whisker_right _ (concat_p1 _)^-1,
  refine _ @ (concat_pp_p _ _ _)^-1,
  apply whisker_left,
  apply eq_con_inv_of_con_eq, symmetry,
  apply con_right_inv_natural
Defined.

Definition elim'_gluel'_pt {P : Type} {Pmk : forall a b, P}
  (Pgl : forall a : A, Pmk a (point _) = Pmk (point _) pt) (Pgr : forall b : B (point _), Pmk (point _) b = Pmk (point _) pt)
  (a : A) (ql : Pgl (point _) = idp) (qr : Pgr (point _) = idp) :
  ap (dsmash.elim' Pmk Pgl Pgr ql qr) (gluel' a (point _)) = Pgl a.
  !elim_gluel' @ whisker_left _ ql⁻²

Definition elim'_gluer'_pt {P : Type} {Pmk : forall a b, P}
  (Pgl : forall a : A, Pmk a (point _) = Pmk (point _) pt) (Pgr : forall b : B (point _), Pmk (point _) b = Pmk (point _) pt)
  (b : B (point _)) (ql : Pgl (point _) = idp) (qr : Pgr (point _) = idp) :
  ap (dsmash.elim' Pmk Pgl Pgr ql qr) (gluer' b (point _)) = Pgr b.
  !elim_gluer' @ whisker_left _ qr⁻²

  protectedDefinition rec_eq {C : Type} {f g : ⋀ B -> C}
  (Pmk : forall a b, f (dsmash.mk a b) = g (dsmash.mk a b))
  (Pl : f auxl = g auxl) (Pr : f auxr = g auxr)
  (Pgl : forall a, square (Pmk a (point _)) Pl (ap f (gluel a)) (ap g (gluel a)))
  (Pgr : forall b, square (Pmk (point _) b) Pr (ap f (gluer b)) (ap g (gluer b))) (x : dsmash' B) : f x = g x.
Proof.
  induction x with a b a b,
  { exact Pmk a b },
  { exact Pl },
  { exact Pr },
  { apply eq_pathover, apply Pgl },
  { apply eq_pathover, apply Pgr }
Defined.

Definition rec_eq_gluel {C : Type} {f g : ⋀ B -> C}
  {Pmk : forall a b, f (dsmash.mk a b) = g (dsmash.mk a b)}
  {Pl : f auxl = g auxl} {Pr : f auxr = g auxr}
  (Pgl : forall a, square (Pmk a (point _)) Pl (ap f (gluel a)) (ap g (gluel a)))
  (Pgr : forall b, square (Pmk (point _) b) Pr (ap f (gluer b)) (ap g (gluer b))) (a : A) :
  natural_square (dsmash.rec_eq Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a.
Proof.
  refine ap square_of_pathover !rec_gluel @ _,
  apply to_right_inv !eq_pathover_equiv_square
Defined.

Definition rec_eq_gluer {C : Type} {f g : ⋀ B -> C}
  {Pmk : forall a b, f (dsmash.mk a b) = g (dsmash.mk a b)}
  {Pl : f auxl = g auxl} {Pr : f auxr = g auxr}
  (Pgl : forall a, square (Pmk a (point _)) Pl (ap f (gluel a)) (ap g (gluel a)))
  (Pgr : forall b, square (Pmk (point _) b) Pr (ap f (gluer b)) (ap g (gluer b))) (b : B (point _)) :
  natural_square (dsmash.rec_eq Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b.
Proof.
  refine ap square_of_pathover !rec_gluer @ _,
  apply to_right_inv !eq_pathover_equiv_square
Defined.

  (* the functorial action of the dependent smash product *)
Definition dsmash_functor' (f : A ->* C) (g : forall , B a ->* D (f a)) : ⋀ B -> ⋀ D.
Proof.
  intro x, induction x,
  { exact dsmash.mk (f a) (g a b) },
  { exact auxl },
  { exact auxr },
  { exact ap (dsmash.mk (f a)) (point_eq (g a)) @ gluel (f a) },
  { exact gluer2 (g (point _) b) (point_eq f) }
Defined.

Definition dsmash_functor (f : A ->* C) (g : forall , B a ->* D (f a)) : ⋀ B ->* ⋀ D.
Proof.
  fapply Build_pMap,
  { exact dsmash_functor' f g } =>
  { exact mk_eq_mk (point_eq f) (point_eq (g (point _)) @po apd (fun a => Point (D a)) (point_eq f)) },
Defined.

  infixr ` ⋀-> `:65 . dsmash_functor

Definition pmap_of_map' (A : pType) {B : Type} (f : A -> B) :
  A ->* pointed.MK B (f (point _)).
  Build_pMap f idp

Definition functor_gluel (f : A ->* C) (g : forall , B a ->* D (f a)) (a : A) :
  ap (f ⋀-> g) (gluel a) = ap (dsmash.mk (f a)) (point_eq (g a)) @ gluel (f a).
  !elim_gluel

Definition functor_gluer (f : A ->* C) (g : forall , B a ->* D (f a)) (b : B (point _)) :
  ap (f ⋀-> g) (gluer b) = gluer2 (g (point _) b) (point_eq f).
  !elim_gluer





  (* the statements of the above rules becomes easier if one of the functions respects the basepoint
  by reflexivity *)






Definition dsmash_functor_pid (B : A -> pType) :
  pid A ⋀-> (fun a => pid (B a)) ==* pid (⋀ B).
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x with a b a b,
  { reflexivity },
  { reflexivity },
  { reflexivity },
  { apply eq_pathover_id_right, apply hdeg_square, exact !functor_gluel @ (concat_1p _) } =>
  { apply eq_pathover_id_right, apply hdeg_square, exact !functor_gluer @ (concat_1p _) }} =>
  { reflexivity }
Defined.

  (* the functorial action of the dependent smash product respects pointed homotopies => and some computation rules for this pointed homotopy *)
Definition dsmash_functor_phomotopy {f f' : A ->* C} {g : forall , B a ->* D (f a)} {g' : forall a, B a ->* D (f' a)}
  (h₁ : f ==* f') (h₂ : forall a, ptransport D (h₁ a) o* g a ==* g' a) : f ⋀-> g ==* f' ⋀-> g'.
Proof.
  induction h₁ using phomotopy_rec_idp,
  --induction h₂ using phomotopy_rec_idp,
  exact sorry --reflexivity
Defined.

  infixr ` ⋀~ `:78 . dsmash_functor_phomotopy

  (* a more explicit proof, if we ever need it *)









  (* the functorial action preserves compositions => the interchange law *)




  (* An alternative proof which doesn't start by applying inductions, so which is more explicit *)





  (* composing commutes with applying homotopies *)


  section
  variables {A₀₀ A₂₀ A₀₂ A₂₂ : pType} {B₀₀ B₂₀ B₀₂ B₂₂ : pType}
  {f₁₀ : A₀₀ ->* A₂₀} {f₀₁ : A₀₀ ->* A₀₂} {f₂₁ : A₂₀ ->* A₂₂} {f₁₂ : A₀₂ ->* A₂₂}
  {g₁₀ : B₀₀ ->* B₂₀} {g₀₁ : B₀₀ ->* B₀₂} {g₂₁ : B₂₀ ->* B₂₂} {g₁₂ : B₀₂ ->* B₂₂}

  (* applying the functorial action of dsmash to squares of pointed maps *)
Defined.

  (* f ∧ g is a pointed equivalence if f and g are *)
Definition dsmash_functor_using_pushout (f : A ->* C) (g : forall , B a ->* D (f a)) :
  ⋀ B -> ⋀ D.
Proof.
  refine pushout.functor (f +-> (transport D (point_eq f) o g (point _))) (sigma_functor f g) id _ _ =>
  { intro v, induction v with a b,
  exact ap (dpair _) (point_eq (g a)),
  exact sigma_eq (point_eq f) !pathover_tr },
  { intro v, induction v with a b: reflexivity }
Defined.

Definition dsmash_functor_homotopy_pushout_functor (f : A ->* C) (g : forall , B a ->* D (f a)) :
  f ⋀-> g == dsmash_functor_using_pushout f g.
Proof.
  intro x, induction x,
  { reflexivity },
  { reflexivity },
  { reflexivity },
  { apply eq_pathover, refine !elim_gluel @ph _ @hp !pushout.elim_glue^-1,
  apply hdeg_square, esimp, apply whisker_right, apply ap_compose },
  { apply eq_pathover, refine !elim_gluer @ph _ @hp !pushout.elim_glue^-1,
  apply hdeg_square, reflexivity }
Defined.

Definition dsmash_pequiv (f : A <~>* C) (g : forall a, B a <~>* D (f a)) : ⋀ B <~>* ⋀ D.
Proof.
  fapply pequiv_of_pmap (f ⋀-> g),
  refine homotopy_closed _ (dsmash_functor_homotopy_pushout_functor f g)^-1ʰᵗʸ _ =>
  apply pushout.is_equiv_functor =>
  { apply is_equiv_sum_functor => apply is_equiv_compose, apply pequiv.to_is_equiv,
  exact to_is_equiv (equiv_ap _ _) },
  apply is_equiv_sigma_functor => intro a, apply pequiv.to_is_equiv
Defined.

  infixr ` ⋀<~> `:80 . dsmash_pequiv

Definition dsmash_pequiv_left (B : C -> pType) (f : A <~>* C) :
  ⋀ (B o f) <~>* ⋀ B.
  f ⋀<~> fun a => pequiv.rfl

Definition dsmash_pequiv_right {D : A -> pType} (g : forall a, B a <~>* D a) : ⋀ B <~>* ⋀ D.
  pequiv.rfl ⋀<~> g

  (* f ∧ g is constant if f is constant *)





  (* We want to show that dsmash_functor_left is natural in A => B and C.

  For this we need two coherence rules. Given the function h . (f' o f) ⋀-> (g' o g) and suppose
  that either f' or f is constant. There are two ways to show that h is constant: either by using
  exchange, or directly. We need to show that these two proofs result in the same pointed
  homotopy. First we do the case where f is constant *)


















































Definition pinr (B : A -> pType) (a : A) : B a ->* ⋀ B.
Proof.
  fapply Build_pMap,
  { intro b, exact dsmash.mk a b },
  { exact gluel' a (point _) }
Defined.

Definition pinl (b : forall a, B a) : A ->* ⋀ B.
Proof.
  fapply Build_pMap,
  { intro a, exact dsmash.mk a (b a) },
  { exact gluer' (b (point _)) (point _) }
Defined.


Definition dsmash_pmap_unit_pt (B : A -> pType) : pinr B (point _) ==* pconst (B (point _)) (⋀ B).
Proof.
  fapply Build_pHomotopy,
  { intro b, exact gluer' b (point _) },
  { rexact con.right_inv (gluer (point _)) @ (con.right_inv (gluel (point _)))^-1 }
Defined.

Definition dsmash_pmap_unit (B : A -> pType) : ppforall (a : A), B a ->** ⋀ B.
Proof.
  fapply ppi.mk,
  { exact pinr B },
  { apply path_pforall, exact dsmash_pmap_unit_pt B }
Defined.

  (* The unit is natural in the first argument *)
Definition dsmash_functor_pid_pinr' (B : A' -> pType) (f : A ->* A') (a : A) :
  pinr B (f a) ==* (f ⋀-> fun a => !pid) o* pinr (B o f) a.
Proof.
  fapply Build_pHomotopy,
  { intro b, reflexivity },
  { refine (concat_1p _) @ _,
  induction A' with A' a₀', induction f with f f₀, esimp at *,
  induction f₀, exact sorry }
Defined.




  (* The unit is also dinatural in the first argument, but that's easier to prove after the adjunction.
  We don't need it for the adjunction *)

  (* The unit-counit laws *)



  (* The underlying (unpointed) functions of the equivalence A ->* (B ->* C) <~>* ⋀ B ->* C) *)













  (* The pointed maps of the equivalence A ->* (B ->* C) <~>* ⋀ B ->* C *)











Definition dsmash_pelim_fn_fn (f : ⋀ B ->* C) (a : A) : B a ->* C.
  Build_pMap (fun b => f (dsmash.mk a b)) (ap f (gluel' a (point _)) @ point_eq f)

Definition dsmash_pelim_fn (f : ⋀ B ->* C) : dbpmap B (fun a => C).
Proof.
  fapply dbBuild_pMap (dsmash_pelim_fn_fn f),
  { intro b, exact ap f (gluer' b (point _)) @ point_eq f },
  { apply whisker_right, apply ap02, exact (con_pV _) @ (con_pV _)^-1 }
Defined.

Definition dsmash_pelim_pmap (B : A -> pType) (C : pType) :
  ppMap (⋀ B) C ->* dbppMap B (fun a => C).
Proof.
  apply Build_pMap dsmash_pelim_fn,
  fapply dbpmap_eq,
  { intro a, exact Build_pHomotopy homotopy.rfl (ap_pp _ _ _)stant^-1 },
  { intro b, exact (ap_pp _ _ _)stant @pv ids },
  { esimp, esimp [whisker_right], exact sorry }
Defined.

Definition dsmash_pelim_pequiv (B : A -> pType) (C : pType) :
  ppMap (⋀ B) C <~>* dbppMap B (fun a => C).
  sorry

set_option pp.binder_types true
open is_trunc

  (* we could also use pushout_arrow_equiv *)
Definition dsmash_arrow_equiv (B : A -> pType) (C : Type) :
  (⋀ B -> C) <~> Σ(f : forall a, B a -> C) (c₁ : C) (c₀ : C), (forall a, f a (point _) = c₀) \* (forall b, f (point _) b = c₁).
Proof.
  fapply equiv.MK,
  { intro f, exact ⟨fun a b => f (dsmash.mk a b), f auxr, f auxl, (fun a => ap f (gluel a), fun b => ap f (gluer b))⟩ },
  { intro x, exact dsmash.elim x.1 x.2.2.1 x.2.1 x.2.2.2.1 x.2.2.2.2 },
  { intro x, induction x with f x, induction x with c₁ x, induction x with c₀ x, induction x with p₁ p₂,
  apply ap (dpair _), apply ap (dpair _), apply ap (dpair _), esimp,
  exact pair_eq (eq_of_homotopy (elim_gluel _ _)) (eq_of_homotopy (elim_gluer _ _)) },
  { intro f, apply eq_of_homotopy, intro x, induction x, reflexivity, reflexivity, reflexivity,
  apply eq_pathover, apply hdeg_square, apply elim_gluel,
  apply eq_pathover, apply hdeg_square, apply elim_gluer }
Defined.

Definition dsmash_arrow_equiv_inv_pt
  (x : Σ(f : forall a, B a -> C) (c₁ : C) (c₀ : C), (forall a, f a (point _) = c₀) \* (forall b, f (point _) b = c₁)) :
  to_inv (dsmash_arrow_equiv B C) x (point _) = x.1 (point _) pt.
  by reflexivity

  open pi

Definition dsmash_pelim_equiv (B : A -> pType) (C : pType) :
  ppMap (⋀ B) C <~> dbppMap B (fun a => C).
Proof.
  refine !pmap.sigma_char @e _,
  refine sigma_equiv_sigma_left !dsmash_arrow_equiv @e _,
  refine sigma_equiv_sigma_right (fun x => equiv_eq_closed_left _ (dsmash_arrow_equiv_inv_pt x)) @e _,
  refine !sigma_assoc_equiv @e _,
  refine sigma_equiv_sigma_right (fun f => !sigma_assoc_equiv @e
  sigma_equiv_sigma_right (fun c₁ => !sigma_assoc_equiv @e
  sigma_equiv_sigma_right (fun c₂ => sigma_equiv_sigma_left !sigma.equiv_prod^-1ᵉ @e
  !sigma_assoc_equiv) @e
  sigma_assoc_equiv_left _ (sigma_homotopy_constant_equiv (point _) (fun a => f a (point _)))^-1ᵉ @e
  sigma_equiv_sigma_right (fun h₁ => !sigma_comm_equiv) @e !sigma_comm_equiv) @e
  sigma_assoc_equiv_left _ (sigma_homotopy_constant_equiv (point _) (f (point _)))^-1ᵉ @e
  sigma_equiv_sigma_right (fun h₂ =>
  sigma_equiv_sigma_right (fun r₂ =>
  sigma_equiv_sigma_right (fun h₁ => !comm_equiv_constant) @e !sigma_comm_equiv) @e
  !sigma_comm_equiv) @e
  !sigma_comm_equiv @e
  sigma_equiv_sigma_right (fun r =>
  sigma_equiv_sigma_left (pi_equiv_pi_right (fun b => equiv_eq_closed_right _ r)) @e
  sigma_equiv_sigma_right (fun h₂ =>
  sigma_equiv_sigma !eq_equiv_con_inv_eq_idp^-1ᵉ (fun r₂ =>
  sigma_equiv_sigma_left (pi_equiv_pi_right (fun a => equiv_eq_closed_right _ r)) @e
  sigma_equiv_sigma_right (fun h₁ => !eq_equiv_con_inv_eq_idp^-1ᵉ)) @e
  !sigma_comm_equiv @e
  sigma_equiv_sigma_right (fun h₁ => !comm_equiv_constant)) @e
  !sigma_comm_equiv) @e
  !sigma_comm_equiv @e sigma_equiv_sigma_right (fun h₁ =>
  !sigma_comm_equiv @e sigma_equiv_sigma_right (fun h₂ =>
  !sigma_sigma_eq_right))) @e _,
  refine !sigma_assoc_equiv' @e _,
  refine sigma_equiv_sigma_left (@sigma_pi_equiv_pi_sigma _ _ (fun a f => f (point _) = (point _)) @e
  pi_equiv_pi_right (fun a => !pmap.sigma_char^-1ᵉ)) @e _,
  exact !dbpmap.sigma_char^-1ᵉ
Defined.

Definition dsmash_pelim_equiv' (B : A -> pType) (C : pType) :
  ppMap (⋀ B) C <~> ppforall a, B a ->** C.
  dsmash_pelim_equiv B C @e (ppi_equiv_dbpmap B (fun a => C))^-1ᵉ


Defined. dsmash
