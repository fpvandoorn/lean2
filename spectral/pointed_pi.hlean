(*
Copyright (c) 2016 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Floris van Doorn
*)

import homotopy.connectedness types.pointed2 .move_to_lib .pointed

open eq pointed equiv sigma is_equiv trunc option pi function fiber

(*
  In this file we define dependent pointed maps and properties of them.

  Using this, we give the truncation level
  of the type of pointed maps, giving the connectivity of
  the domain and the truncation level of the codomain.
  This is is_trunc_pmap_of_is_conn at the end.

  We also prove other properties about pointed (dependent maps), like the fact that
  (ppforall a, F a) -> (ppforall a, X a) -> (ppforall a, B a)
  is a fibration sequence if (F a) -> (X a) -> B a) is.
*)

namespace pointed

  (* the pointed type of unpointed (nondependent) maps *)
Definition pumap (A : Type) (B : pType) : pType.
  pointed.MK (A -> B) (const A (point _))

  (* the pointed type of unpointed dependent maps *)
Definition pupi {A : Type} (B : A -> pType) : pType.
  pointed.MK (forall a, B a) (fun a => (point _))

  notation `forall ᵘ*` binders `, ` r:(scoped P, pupi P) . r
  infix ` ->ᵘ* `:30 . pumap

  (* stuff about the pointed type of unpointed maps (dependent and non-dependent) *)
Definition sigma_pumap {A : Type} (B : A -> Type) (C : pType) :
  ((Σa, B a) ->ᵘ* C) <~>* forall ᵘ*a, B a ->ᵘ* C.
  pequiv_of_equiv (equiv_sigma_rec _)^-1ᵉ idp

Definition phomotopy_mk_pupi {A : pType} {B : Type} {C : B -> pType}
  {f g : A ->* (forall ᵘ*b, C b)} (p : f ~2 g)
  (q : p (point _) @hty apd10 (point_eq g) == apd10 (point_eq f)) : f ==* g.
Proof.
  apply Build_pHomotopy (fun a => eq_of_homotopy (p a)),
  apply inj !eq_equiv_homotopy,
  apply eq_of_homotopy, intro b,
  refine !apd10_con @ _,
  refine whisker_right _ !apd10_eq_of_homotopy @ q b
Defined.

Definition pupi_functor {A A' : Type} {B : A -> pType} {B' : A' -> pType}
  (f : A' -> A) (g : forall a, B (f a) ->* B' a) : (forall ᵘ*a, B a) ->* (forall ᵘ*a', B' a').
  Build_pMap (pi_functor f g) (eq_of_homotopy (fun a => point_eq (g a)))

Definition pupi_functor_right {A : Type} {B B' : A -> pType}
  (g : forall a, B a ->* B' a) : (forall ᵘ*a, B a) ->* (forall ᵘ*a, B' a).
  pupi_functor id g

Definition pupi_functor_compose {A A' A'' : Type}
  {B : A -> pType} {B' : A' -> pType} {B'' : A'' -> pType} (f : A'' -> A') (f' : A' -> A)
  (g' : forall a, B' (f a) ->* B'' a) (g : forall a, B (f' a) ->* B' a) :
  pupi_functor (f' o f) (fun a => g' a o* g (f a)) ==* pupi_functor f g' o* pupi_functor f' g.
Proof.
  fapply phomotopy_mk_pupi,
  { intro h a, reflexivity },
  { intro a, refine (concat_1p _) @ _, refine !apd10_con @ _ @ !apd10_eq_of_homotopy^-1, esimp,
  refine (!apd10_prepostcompose @ ap02 (g' a) !apd10_eq_of_homotopy) ◾
  !apd10_eq_of_homotopy }
Defined.

Definition pupi_functor_pid (A : Type) (B : A -> pType) :
  pupi_functor id (fun a => pid (B a)) ==* pid (forall ᵘ*a, B a).
Proof.
  fapply phomotopy_mk_pupi,
  { intro h a, reflexivity },
  { intro a, refine (concat_1p _) @ !apd10_eq_of_homotopy^-1 }
Defined.

Definition pupi_functor_phomotopy {A A' : Type} {B : A -> pType} {B' : A' -> pType}
  {f f' : A' -> A} {g : forall a, B (f a) ->* B' a} {g' : forall a, B (f' a) ->* B' a}
  (p : f == f') (q : forall a, g a ==* g' a o* ptransport B (p a)) :
  pupi_functor f g ==* pupi_functor f' g'.
Proof.
  fapply phomotopy_mk_pupi,
  { intro h a, exact q a (h (f a)) @ ap (g' a) (apdt h (p a)) },
  { intro a, esimp,
  exact whisker_left _ !apd10_eq_of_homotopy @ (concat_pp_p _ _ _) @
  point_htpy (q a) @ !apd10_eq_of_homotopy^-1 }
Defined.

Definition pupi_pequiv {A A' : Type} {B : A -> pType} {B' : A' -> pType}
  (e : A' <~> A) (f : forall a, B (e a) <~>* B' a) :
  (forall ᵘ*a, B a) <~>* (forall ᵘ*a', B' a').
  pequiv.MK (pupi_functor e f)
  (pupi_functor e^-1ᵉ (fun a => ptransport B (right_inv e a) o* (f (e^-1ᵉ a))^-1ᵉ*))
  abstract begin
  refine !pupi_functor_compose^-1* @* pupi_functor_phomotopy (to_right_inv e) _ @*
  !pupi_functor_pid =>
  intro a, exact !pinv_pcompose_cancel_right @* !pid_pcompose^-1*
Defined. end
  abstract begin
  refine !pupi_functor_compose^-1* @* pupi_functor_phomotopy (to_left_inv e) _ @*
  !pupi_functor_pid =>
  intro a, refine !passoc^-1* @* pinv_right_phomotopy_of_phomotopy _ @* !pid_pcompose^-1*,
  refine pwhisker_left _ _ @* !ptransport_natural,
  exact ptransport_change_eq _ (adj e a) @* ptransport_ap B e (to_left_inv e a)
Defined. end

Definition pupi_pequiv_right {A : Type} {B B' : A -> pType} (f : forall a, B a <~>* B' a) :
  (forall ᵘ*a, B a) <~>* (forall ᵘ*a, B' a).
  pupi_pequiv erfl f

Definition loop_pupi {A : Type} (B : A -> pType) : loops (forall ᵘ*a, B a) <~>* forall ᵘ*a, loops (B a).
  pequiv_of_equiv !eq_equiv_homotopy idp


Definition ap1_gen_pi {A A' : Type} {B : A -> Type} {B' : A' -> Type}
  {h₀ h₁ : forall a, B a} {h₀' h₁' : forall a', B' a'} (f : A' -> A) (g : forall a, B (f a) -> B' a)
  (p₀ : pi_functor f g h₀ == h₀') (p₁ : pi_functor f g h₁ == h₁') (r : h₀ = h₁) (a' : A') :
  apd10 (ap1_gen (pi_functor f g) (eq_of_homotopy p₀) (eq_of_homotopy p₁) r) a' =
  ap1_gen (g a') (p₀ a') (p₁ a') (apd10 r (f a')).
Proof.
  induction r, induction p₀ using homotopy.rec_idp, induction p₁ using homotopy.rec_idp, esimp,
  exact apd10 (ap apd10 !ap1_gen_idp) a',


Defined.

Definition ap1_gen_pi_idp {A A' : Type} {B : A -> Type} {B' : A' -> Type}
  {h₀ : forall a, B a} (f : A' -> A) (g : forall a, B (f a) -> B' a) (a' : A') :
  ap1_gen_pi f g (homotopy.refl (pi_functor f g h₀)) (homotopy.refl (pi_functor f g h₀)) idp a' =
  apd10 (ap apd10 !ap1_gen_idp) a'.
Proof.
  esimp [ap1_gen_pi],
  refine !homotopy_rec_idp_refl @ !homotopy_rec_idp_refl,
Defined.

Definition loop_pupi_natural {A : Type} {B B' : A -> pType} (f : forall a, B a ->* B' a) :
  psquare (Ω-> (pupi_functor_right f)) (pupi_functor_right (fun a => Ω-> (f a)))
  (loop_pupi B) (loop_pupi B').
Proof.
  fapply phomotopy_mk_pupi,
  { intro p a, exact ap1_gen_pi id f (fun a => point_eq (f a)) (fun a => point_eq (f a)) p a },
  { intro a, revert B' f, refine fiberwise_pointed_map_rec _ _, intro B' f,
  refine !ap1_gen_pi_idp ◾ (ap (fun x => apd10 x _) (concat_1p _) @ !apd10_eq_of_homotopy) }
Defined.

Definition phomotopy_mk_pumap {A C : pType} {B : Type} {f g : A ->* (B ->ᵘ* C)}
  (p : f ~2 g) (q : p (point _) @hty apd10 (point_eq g) == apd10 (point_eq f))
  : f ==* g.
  phomotopy_mk_pupi p q

Definition pumap_functor {A A' : Type} {B B' : pType} (f : A' -> A) (g : B ->* B') :
  (A ->ᵘ* B) ->* (A' ->ᵘ* B').
  pupi_functor f (fun a => g)

Definition pumap_functor_compose {A A' A'' : Type} {B B' B'' : pType}
  (f : A'' -> A') (f' : A' -> A) (g' : B' ->* B'') (g : B ->* B') :
  pumap_functor (f' o f) (g' o* g) ==* pumap_functor f g' o* pumap_functor f' g.
  pupi_functor_compose f f' (fun a => g') (fun a => g)

Definition pumap_functor_pid (A : Type) (B : pType) :
  pumap_functor id (pid B) ==* pid (A ->ᵘ* B).
  pupi_functor_pid A (fun a => B)

Definition pumap_functor_phomotopy {A A' : Type} {B B' : pType} {f f' : A' -> A} {g g' : B ->* B'}
  (p : f == f') (q : g ==* g') : pumap_functor f g ==* pumap_functor f' g'.
  pupi_functor_phomotopy p (fun a => q @* !pcompose_pid^-1* @* pwhisker_left _ !ptransport_constant^-1*)

Definition pumap_pequiv {A A' : Type} {B B' : pType} (e : A <~> A') (f : B <~>* B') :
  (A ->ᵘ* B) <~>* (A' ->ᵘ* B').
  pupi_pequiv e^-1ᵉ (fun a => f)

Definition pumap_pequiv_right (A : Type) {B B' : pType} (f : B <~>* B') :
  (A ->ᵘ* B) <~>* (A ->ᵘ* B').
  pumap_pequiv erfl f

Definition pumap_pequiv_left {A A' : Type} (B : pType) (f : A <~> A') :
  (A ->ᵘ* B) <~>* (A' ->ᵘ* B).
  pumap_pequiv f pequiv.rfl

Definition loop_pumap (A : Type) (B : pType) : loops (A ->ᵘ* B) <~>* A ->ᵘ* loops B.
  loop_pupi (fun a => B)

  (* the pointed sigma type *)
Definition psigma_gen {A : pType} (P : A -> Type) (x : P (point _)) : pType.
  pointed.MK (Σa, P a) ⟨(point _), x⟩

Definition psigma_gen_functor {A A' : pType} {B : A -> Type}
  {B' : A' -> Type} {b : B (point _)} {b' : B' (point _)} (f : A ->* A')
  (g : forall a, B a -> B' (f a)) (p : g (point _) b =[point_eq f] b') : psigma_gen B b ->* psigma_gen B' b'.
  Build_pMap (sigma_functor f g) (sigma_eq (point_eq f) p)

Definition psigma_gen_functor_right {A : pType} {B B' : A -> Type}
  {b : B (point _)} {b' : B' (point _)} (f : forall a, B a -> B' a) (p : f (point _) b = b') :
  psigma_gen B b ->* psigma_gen B' b'.
  proof Build_pMap (sigma_functor id f) (sigma_eq_right p) qed

Definition psigma_gen_pequiv_psigma_gen {A A' : pType} {B : A -> Type}
  {B' : A' -> Type} {b : B (point _)} {b' : B' (point _)} (f : A <~>* A')
  (g : forall a, B a <~> B' (f a)) (p : g (point _) b =[point_eq f] b') : psigma_gen B b <~>* psigma_gen B' b'.
  pequiv_of_equiv (sigma_equiv_sigma f g) (sigma_eq (point_eq f) p)

Definition psigma_gen_pequiv_psigma_gen_left {A A' : pType} {B : A' -> Type}
  {b : B (point _)} (f : A <~>* A') {b' : B (f (point _))} (q : b' =[point_eq f] b) :
  psigma_gen (B o f) b' <~>* psigma_gen B b.
  psigma_gen_pequiv_psigma_gen f (fun a => erfl) q

Definition psigma_gen_pequiv_psigma_gen_right {A : pType} {B B' : A -> Type}
  {b : B (point _)} {b' : B' (point _)} (f : forall a, B a <~> B' a) (p : f (point _) b = b') :
  psigma_gen B b <~>* psigma_gen B' b'.
  psigma_gen_pequiv_psigma_gen pequiv.rfl f (pathover_idp_of_eq p)

Definition psigma_gen_pequiv_psigma_gen_basepoint {A : pType} {B : A -> Type}
  {b b' : B (point _)} (p : b = b') : psigma_gen B b <~>* psigma_gen B b'.
  psigma_gen_pequiv_psigma_gen_right (fun a => erfl) p

Definition loop_psigma_gen {A : pType} (B : A -> Type) (b₀ : B (point _)) :
  loops (psigma_gen B b₀) <~>* @psigma_gen (loops A) (fun p => pathover B b₀ p b₀) idpo.
  pequiv_of_equiv (sigma_eq_equiv (point _) pt) idp

  open sigma.ops
Definition ap1_gen_sigma {A A' : Type} {B : A -> Type} {B' : A' -> Type}
  {x₀ x₁ : Σa, B a} {a₀' a₁' : A'} {b₀' : B' a₀'} {b₁' : B' a₁'} (f : A -> A')
  (p₀ : f x₀.1 = a₀') (p₁ : f x₁.1 = a₁') (g : forall a, B a -> B' (f a))
  (q₀ : g x₀.1 x₀.2 =[p₀] b₀') (q₁ : g x₁.1 x₁.2 =[p₁] b₁') (r : x₀ = x₁) :
  (fun x => ⟨x..1, x..2⟩) (ap1_gen (sigma_functor f g) (sigma_eq p₀ q₀) (sigma_eq p₁ q₁) r) =
  ⟨ap1_gen f p₀ p₁ r..1, q₀^-1ᵒ @o pathover_ap B' f (apo g r..2) @o q₁⟩.
Proof.
  induction r, induction q₀, induction q₁, reflexivity
Defined.

Definition loop_psigma_gen_natural {A A' : pType} {B : A -> Type}
  {B' : A' -> Type} {b : B (point _)} {b' : B' (point _)} (f : A ->* A')
  (g : forall a, B a -> B' (f a)) (p : g (point _) b =[point_eq f] b') :
  psquare (Ω-> (psigma_gen_functor f g p))
  (psigma_gen_functor (Ω-> f) (fun q r => p^-1ᵒ @o pathover_ap _ _ (apo g r) @o p)
  !cono.left_inv)
  (loop_psigma_gen B b) (loop_psigma_gen B' b').
Proof.
  fapply Build_pHomotopy,
  { exact ap1_gen_sigma f (point_eq f) (point_eq f) g p p },
  { induction f with f f₀, induction A' with A' a₀', esimp at * ⊢, induction p, reflexivity }
Defined.

Definition psigma_gen_functor_pcompose {A₁ A₂ A₃ : pType}
  {B₁ : A₁ -> Type} {B₂ : A₂ -> Type} {B₃ : A₃ -> Type}
  {b₁ : B₁ (point _)} {b₂ : B₂ (point _)} {b₃ : B₃ (point _)}
  {f₁ : A₁ ->* A₂} {f₂ : A₂ ->* A₃}
  (g₁ : forall (a), B₁ a -> B₂ (f₁ a)) (g₂ : forall (a), B₂ a -> B₃ (f₂ a))
  (p₁ : pathover B₂ (g₁ b₁) (point_eq f₁) b₂)
  (p₂ : pathover B₃ (g₂ b₂) (point_eq f₂) b₃) :
  psigma_gen_functor (f₂ o* f₁) (fun a => @g₂ (f₁ a) o @g₁ a) (pathover_ap B₃ f₂ (apo g₂ p₁) @o p₂) ==*
  psigma_gen_functor f₂ g₂ p₂ o* psigma_gen_functor f₁ g₁ p₁.
Proof.
  fapply Build_pHomotopy,
  { intro x, reflexivity },
  { refine (concat_1p _) @ _, esimp,
  refine whisker_right _ !ap_sigma_functor_sigma_eq @ _ =>
  induction f₁ with f₁ f₁₀, induction f₂ with f₂ f₂₀, induction A₂ with A₂ a₂₀,
  induction A₃ with A₃ a₃₀, esimp at * ⊢, induction p₁, induction p₂, reflexivity }
Defined.

Definition psigma_gen_functor_phomotopy {A₁ A₂ : pType}
  {B₁ : A₁ -> Type} {B₂ : A₂ -> Type} {b₁ : B₁ (point _)} {b₂ : B₂ (point _)} {f₁ f₂ : A₁ ->* A₂}
  {g₁ : forall (a), B₁ a -> B₂ (f₁ a)} {g₂ : forall (a), B₁ a -> B₂ (f₂ a)}
  {p₁ : pathover B₂ (g₁ b₁) (point_eq f₁) b₂} {p₂ : pathover B₂ (g₂ b₁) (point_eq f₂) b₂}
  (h₁ : f₁ ==* f₂)
  (h₂ : forall (a) (b : B₁ a), pathover B₂ (g₁ b) (h₁ a) (g₂ b))
  (h₃ : squareover B₂ (square_of_eq (point_htpy h₁)^-1) p₁ p₂ (h₂ b₁) idpo) :
  psigma_gen_functor f₁ g₁ p₁ ==* psigma_gen_functor f₂ g₂ p₂.
Proof.
  induction h₁ using phomotopy_rec_idp,
  fapply Build_pHomotopy,
  { intro x, induction x with a b, exact ap (dpair (f₁ a)) (eq_of_pathover_idp (h₂ b)) },
  { induction f₁ with f f₀, induction A₂ with A₂ a₂₀, esimp at * ⊢,
  induction f₀, esimp, induction p₂ using idp_rec_on,
  rewrite [to_right_inv !eq_con_inv_equiv_con_eq at h₃],
  have h₂ b₁ = p₁, from (eq_top_of_squareover h₃)^-1, induction this,
  refine !ap_dpair @ ap (sigma_eq _) _, exact to_left_inv !pathover_idp (h₂ b₁) }
Defined.

Definition psigma_gen_functor_psquare {A₀₀ A₀₂ A₂₀ A₂₂ : pType}
  {B₀₀ : A₀₀ -> Type} {B₀₂ : A₀₂ -> Type} {B₂₀ : A₂₀ -> Type} {B₂₂ : A₂₂ -> Type}
  {b₀₀ : B₀₀ (point _)} {b₀₂ : B₀₂ (point _)} {b₂₀ : B₂₀ (point _)} {b₂₂ : B₂₂ (point _)}
  {f₀₁ : A₀₀ ->* A₀₂} {f₁₀ : A₀₀ ->* A₂₀} {f₂₁ : A₂₀ ->* A₂₂} {f₁₂ : A₀₂ ->* A₂₂}
  {g₀₁ : forall (a), B₀₀ a -> B₀₂ (f₀₁ a)} {g₁₀ : forall (a), B₀₀ a -> B₂₀ (f₁₀ a)}
  {g₂₁ : forall (a), B₂₀ a -> B₂₂ (f₂₁ a)} {g₁₂ : forall (a), B₀₂ a -> B₂₂ (f₁₂ a)}
  {p₀₁ : pathover B₀₂ (g₀₁ b₀₀) (point_eq f₀₁) b₀₂}
  {p₁₀ : pathover B₂₀ (g₁₀ b₀₀) (point_eq f₁₀) b₂₀}
  {p₂₁ : pathover B₂₂ (g₂₁ b₂₀) (point_eq f₂₁) b₂₂}
  {p₁₂ : pathover B₂₂ (g₁₂ b₀₂) (point_eq f₁₂) b₂₂}
  (h₁ : psquare f₁₀ f₁₂ f₀₁ f₂₁)
  (h₂ : forall (a) (b : B₀₀ a), pathover B₂₂ (g₂₁ (g₁₀ b)) (h₁ a) (g₁₂ (g₀₁ b)))
  (h₃ : squareover B₂₂ (square_of_eq (point_htpy h₁)^-1)
  (pathover_ap B₂₂ f₂₁ (apo g₂₁ p₁₀) @o p₂₁)
  (pathover_ap B₂₂ f₁₂ (apo g₁₂ p₀₁) @o p₁₂)
  (h₂ b₀₀) idpo) :
  psquare (psigma_gen_functor f₁₀ g₁₀ p₁₀) (psigma_gen_functor f₁₂ g₁₂ p₁₂)
  (psigma_gen_functor f₀₁ g₀₁ p₀₁) (psigma_gen_functor f₂₁ g₂₁ p₂₁).
  proof
  !psigma_gen_functor_pcompose^-1* @*
  psigma_gen_functor_phomotopy h₁ h₂ h₃ @*
  !psigma_gen_functor_pcompose
  qed


Defined. pointed open pointed

namespace pointed

Definition pointed_point_eq [instance] {A B : pType} (f : A ->* B) :
  pointed (f (point _) = (point _)).
  pointed.mk (point_eq f)

Definition ppi_of_phomotopy {A B : pType} {f g : A ->* B} (h : f ==* g) :
  ppi (fun x => f x = g x) (point_eq f @ (point_eq g)^-1).
  h

Definition phomotopy {A : pType} {P : A -> Type} {x : P (point _)} (f g : ppi P x) : Type.
  ppi (fun a => f a = g a) (point_eq f @ (point_eq g)^-1)

  variables {A A' A'' : pType} {P Q R : A -> pType} {P' : A' -> pType} {f g h : ppforall a, P a}
  {B C D : A -> Type} {b₀ : B (point _)} {c₀ : C (point _)} {d₀ : D (point _)}
  {k k' l m : ppi B b₀}

Definition pppi_equiv_pmap (A B : pType) : (ppforall (a : A), B) <~> (A ->* B).
  by reflexivity

Definition pppi_pequiv_ppMap (A B : pType) : (ppforall (a : A), B) <~>* ppMap A B.
  by reflexivity

Definition apd10_to_fun_path_pforall (h : f ==* g)
  : apd10 (ap (fun k => pppi.to_fun k) (path_pforall h)) = h.
Proof.
  induction h using phomotopy_rec_idp,
  xrewrite [path_pforall_refl f]
Defined.


Definition phomotopy_mk_ppi {A : pType} {B : pType} {C : B -> pType}
  {f g : A ->* (ppforall b, C b)} (p : forall a, f a ==* g a)
  (q : p (point _) @* phomotopy_path (point_eq g) = phomotopy_path (point_eq f)) : f ==* g.
Proof.
  apply Build_pHomotopy (fun a => path_pforall (p a)),
  apply inj !ppi_eq_equiv,
  refine !phomotopy_path_con @ _, esimp,
  refine ap (fun x => x @* _) !phomotopy_path_of_phomotopy @ q
Defined.


  variable {k}

  variables (k l)

Definition ppi_loop_equiv : (k = k) <~> ppforall (a : A), loops (Build_pType (B a) (k a)).
Proof.
  induction k with k p, induction p,
  exact ppi_eq_equiv (ppi.mk k idp) (ppi.mk k idp)
Defined.

  variables {k l}

Definition ppi_functor_right {A : pType} {B B' : A -> Type}
  {b : B (point _)} {b' : B' (point _)} (f : forall a, B a -> B' a) (p : f (point _) b = b') (g : ppi B b)
  : ppi B' b'.
  ppi.mk (fun a => f a (g a)) (ap (f (point _)) (point_eq g) @ p)

Definition ppi_functor_right_compose {A : pType} {B₁ B₂ B₃ : A -> Type}
  {b₁ : B₁ (point _)} {b₂ : B₂ (point _)} {b₃ : B₃ (point _)} (f₂ : forall a, B₂ a -> B₃ a) (p₂ : f₂ (point _) b₂ = b₃)
  (f₁ : forall a, B₁ a -> B₂ a) (p₁ : f₁ (point _) b₁ = b₂)
  (g : ppi B₁ b₁) : ppi_functor_right (fun a => f₂ a o f₁ a) (ap (f₂ (point _)) p₁ @ p₂) g ==*
  ppi_functor_right f₂ p₂ (ppi_functor_right f₁ p₁ g).
Proof.
  fapply Build_pHomotopy,
  { reflexivity },
  { induction p₁, induction p₂, exact (concat_1p _) @ !ap_compose^-1 }
Defined.

Definition ppi_functor_right_id {A : pType} {B : A -> Type}
  {b : B (point _)} (g : ppi B b) : ppi_functor_right (fun a => id) idp g ==* g.
Proof.
  fapply Build_pHomotopy,
  { reflexivity },
  { reflexivity }
Defined.

Definition ppi_functor_right_phomotopy {g g' : forall , B a -> C a}
  {g₀ : g (point _) b₀ = c₀} {g₀' : g' (point _) b₀ = c₀} {f f' : ppi B b₀}
  (p : g ~2 g') (q : f ==* f') (r : p (point _) b₀ @ g₀' = g₀) :
  ppi_functor_right g g₀ f ==* ppi_functor_right g' g₀' f'.
  Build_pHomotopy (fun a => p a (f a) @ ap (g' a) (q a))
  abstract begin
  induction q using phomotopy_rec_idp,
  induction r, revert g p, refine rec_idp_of_equiv _ homotopy2.rfl _ _ _,
  { intro h h', exact !eq_equiv_eq_symm @e !eq_equiv_homotopy2 },
  { reflexivity },
  induction g₀', induction f with f f₀, induction f₀, reflexivity
Defined. end

Definition ppi_functor_right_phomotopy_refl (g : forall , B a -> C a)
  (g₀ : g (point _) b₀ = c₀) (f : ppi B b₀) :
  ppi_functor_right_phomotopy (homotopy2.refl g) (reflexivity f) (concat_1p _) =
  reflexivity (ppi_functor_right g g₀ f).
Proof.
  induction g₀,
  apply ap (Build_pHomotopy homotopy.rfl),
  refine !phomotopy_rec_idp_refl @ _,
  esimp,
  refine !rec_idp_of_equiv_idp @ _,
  induction f with f f₀, induction f₀, reflexivity
Defined.

Definition ppi_equiv_ppi_right {A : pType} {B B' : A -> Type}
  {b : B (point _)} {b' : B' (point _)} (f : forall a, B a <~> B' a) (p : f (point _) b = b') :
  ppi B b <~> ppi B' b'.
  equiv.MK (ppi_functor_right f p) (ppi_functor_right (fun a => (f a)^-1ᵉ) (inv_eq_of_eq p^-1))
  abstract begin
  intro g, apply path_pforall,
  refine !ppi_functor_right_compose^-1* @* _ =>
  refine ppi_functor_right_phomotopy (fun a => to_right_inv (f a)) (reflexivity g) _ @*
  !ppi_functor_right_id => induction p, exact adj (f (point _)) b @ ap02 (f (point _)) (concat_1p _)^-1

Defined. end
  abstract begin
  intro g, apply path_pforall,
  refine !ppi_functor_right_compose^-1* @* _ =>
  refine ppi_functor_right_phomotopy (fun a => to_left_inv (f a)) (reflexivity g) _ @*
  !ppi_functor_right_id => induction p, exact ((concat_1p _) @ (concat_1p _))^-1,
Defined. end

Definition ppi_equiv_ppi_basepoint {A : pType} {B : A -> Type} {b b' : B (point _)}
  (p : b = b') : ppi B b <~> ppi B b'.
  ppi_equiv_ppi_right (fun a => erfl) p

Definition pmap_compose_ppi (g : forall (a : A), ppMap (P a) (Q a))
  (f : ppforall (a : A), P a) : ppforall (a : A), Q a.
  ppi_functor_right g (point_eq (g (point _))) f

Definition ppi_compose_pmap (g : ppforall (a : A), P a) (f : A' ->* A) :
  ppforall (a' : A'), P (f a').
  ppi.mk (fun a' => g (f a'))
  (eq_of_pathover_idp  (change_path (con_pV _)
  (apd g (point_eq f) @op point_eq g @o (apd (fun x => Point (P x)) (point_eq f))^-1ᵒ)))
(* alternate proof for respecting the point *)

Definition ppi_compose_pmap_phomotopy (g : A ->* A'') (f : A' ->* A) :
  ppi_compose_pmap g f ==* g o* f.
Proof.
  refine Build_pHomotopy homotopy.rfl _,
  refine (concat_1p _) @ _, esimp,
  symmetry,
  refine !eq_of_pathover_idp_constant @ _,
  refine !eq_of_pathover_change_path @ !eq_of_pathover_cono @ _,
  refine (!eq_of_pathover_concato_eq @ !apd_eq_ap ◾ idp) ◾
  (!eq_of_pathover_invo @ (!apd_eq_ap @ (ap_pp _ _ _)stant)⁻²) @ _,
  reflexivity
Defined.

Definition pmap_compose_ppi_ppi_const (g : forall (a : A), ppMap (P a) (Q a)) :
  pmap_compose_ppi g (ppi_const P) ==* ppi_const Q.
  proof Build_pHomotopy (fun a => point_eq (g a)) (concat_1p _)^-1 qed

Definition pmap_compose_ppi_pconst (f : ppforall (a : A), P a) :
  pmap_compose_ppi (fun a => pconst (P a) (Q a)) f ==* ppi_const Q.
  Build_pHomotopy homotopy.rfl (ap_pp _ _ _)stant^-1

Definition ppi_compose_pmap_ppi_const (f : A' ->* A) :
  ppi_compose_pmap (ppi_const P) f ==* ppi_const (P o f).
  Build_pHomotopy homotopy.rfl
Proof.
  exact (ap eq_of_pathover_idp (change_path_of_pathover _ _ _ !cono.right_inv))^-1,
Defined.

Definition ppi_compose_pmap_pconst (g : ppforall (a : A), P a) :
  ppi_compose_pmap g (pconst A' A) ==* pconst A' (P (point _)).
  Build_pHomotopy (fun a => point_eq g) !idpo_concato_eq^-1

Definition pmap_compose_ppi2 {g g' : forall (a : A), ppMap (P a) (Q a)}
  {f f' : ppforall (a : A), P a} (p : forall a, g a ==* g' a) (q : f ==* f') :
  pmap_compose_ppi g f ==* pmap_compose_ppi g' f'.
  ppi_functor_right_phomotopy p q (point_htpy (p (point _)))

Definition pmap_compose_ppi2_refl (g : forall (a : A), P a ->* Q a) (f : ppforall (a : A), P a) :
  pmap_compose_ppi2 (fun a => reflexivity (g a)) (reflexivity f) = (reflexivity _).
Proof.
  refine _ @ ppi_functor_right_phomotopy_refl g (point_eq (g (point _))) f =>
  exact ap (ppi_functor_right_phomotopy _ _) (to_right_inv !eq_con_inv_equiv_con_eq _)
Defined.

Definition pmap_compose_ppi_phomotopy_left {g g' : forall (a : A), ppMap (P a) (Q a)}
  (f : ppforall (a : A), P a) (p : forall a, g a ==* g' a) : pmap_compose_ppi g f ==* pmap_compose_ppi g' f.
  pmap_compose_ppi2 p (reflexivity _)

Definition pmap_compose_ppi_phomotopy_right (g : forall (a : A), ppMap (P a) (Q a))
  {f f' : ppforall (a : A), P a} (p : f ==* f') : pmap_compose_ppi g f ==* pmap_compose_ppi g f'.
  pmap_compose_ppi2 (fun a => (reflexivity _)) p

Definition pmap_compose_ppi_pid_left
  (f : ppforall (a : A), P a) : pmap_compose_ppi (fun a => pid (P a)) f ==* f.
  Build_pHomotopy homotopy.rfl idp

Definition pmap_compose_ppi_pcompose (h : forall (a : A), ppMap (Q a) (R a))
  (g : forall (a : A), ppMap (P a) (Q a)) :
  pmap_compose_ppi (fun a => h a o* g a) f ==* pmap_compose_ppi h (pmap_compose_ppi g f) .
  Build_pHomotopy homotopy.rfl
  abstract (concat_1p _) @ whisker_right _ ((ap_pp _ _ _) @ whisker_right _ !ap_compose') @ (concat_pp_p _ _ _) end

Definition ppi_assoc (h : forall (a : A), Q a ->* R a) (g : forall (a : A), P a ->* Q a)
  (f : ppforall a, P a) :
  pmap_compose_ppi (fun a => h a o* g a) f ==* pmap_compose_ppi h (pmap_compose_ppi g f).
Proof.
  fapply Build_pHomotopy,
  { intro a, reflexivity },
  exact (concat_1p _) @ whisker_right _ ((ap_pp _ _ _) @ whisker_right _ !ap_compose^-1) @ (concat_pp_p _ _ _)
Defined.

Definition pmap_compose_ppi_path_pforall (g : forall a, P a ->* Q a) {f f' : ppforall a, P a} (p : f ==* f') :
  ap (pmap_compose_ppi g) (path_pforall p) =
  path_pforall (pmap_compose_ppi_phomotopy_right g p).
Proof.
  induction p using phomotopy_rec_idp,
  refine ap02 _ !path_pforall_refl @ !path_pforall_refl^-1 @ ap path_pforall _,
  exact !pmap_compose_ppi2_refl^-1
Defined.

Definition ppi_assoc_ppi_const_right (g : forall a, Q a ->* R a) (f : forall a, P a ->* Q a) :
  ppi_assoc g f (ppi_const P) @*
  (pmap_compose_ppi_phomotopy_right _ (pmap_compose_ppi_ppi_const f) @*
  pmap_compose_ppi_ppi_const g) = pmap_compose_ppi_ppi_const (fun a => g a o* f a).
Proof.
  revert R g, refine fiberwise_pointed_map_rec _ _,
  revert Q f, refine fiberwise_pointed_map_rec _ _,
  intro Q f R g,
  refine ap (fun x => _ @* (x @* _)) !pmap_compose_ppi2_refl @ _,
  reflexivity
Defined.

Definition pppi_compose_left (g : forall (a : A), ppMap (P a) (Q a)) :
  (ppforall (a : A), P a) ->* ppforall (a : A), Q a.
  Build_pMap (pmap_compose_ppi g) (path_pforall (pmap_compose_ppi_ppi_const g))

Definition pppi_compose_right (f : A' ->* A) :
  (ppforall (a : A), P a) ->* ppforall (a' : A'), P (f a').
  Build_pMap (fun h => ppi_compose_pmap h f) (path_pforall (ppi_compose_pmap_ppi_const f))

Definition pppi_compose_right_phomotopy (f : A' ->* A) :
  pppi_compose_right f ==* @ppcompose_right _ _ A'' f.
Proof.
  fapply phomotopy_mk_ppMap,
  { intro g, exact ppi_compose_pmap_phomotopy g f },
  { exact sorry }
Defined.

Definition pppi_compose_left_pcompose (g : forall (a : A), Q a ->* R a) (f : forall (a : A), P a ->* Q a)
  : pppi_compose_left (fun a => g a o* f a) ==* (pppi_compose_left g o* pppi_compose_left f).
Proof.
  fapply phomotopy_mk_ppi,
  { exact ppi_assoc g f },
  { refine idp ◾** (!phomotopy_path_con @
  (ap phomotopy_path !pmap_compose_ppi_path_pforall @ !phomotopy_path_of_phomotopy) ◾**
  !phomotopy_path_of_phomotopy) @ _ @ !phomotopy_path_of_phomotopy^-1,
  apply ppi_assoc_ppi_const_right },
Defined.

Definition pppi_compose_left_phomotopy {g g' : forall (a : A), ppMap (P a) (Q a)}
  (p : forall a, g a ==* g' a) : pppi_compose_left g ==* pppi_compose_left g'.
Proof.
  apply phomotopy_path, apply ap pppi_compose_left, apply eq_of_homotopy, intro a,
  apply path_pforall, exact p a
Defined.

Definition psquare_pppi_compose_left {A : pType} {B C D E : A -> pType}
  {ftop : forall (a : A), B a ->* C a} {fbot : forall (a : A), D a ->* E a}
  {fleft : forall (a : A), B a ->* D a} {fright : forall (a : A), C a ->* E a}
  (psq : forall (a :A), psquare (ftop a) (fbot a) (fleft a) (fright a))
  : psquare
  (pppi_compose_left ftop)
  (pppi_compose_left fbot)
  (pppi_compose_left fleft)
  (pppi_compose_left fright)
 .
Proof.
  refine (pppi_compose_left_pcompose fright ftop)^-1* @* _ @*
  (pppi_compose_left_pcompose fbot fleft),
  exact pppi_compose_left_phomotopy psq
Defined.

Definition ppi_pequiv_right (g : forall (a : A), P a <~>* Q a) :
  (ppforall (a : A), P a) <~>* ppforall (a : A), Q a.
Proof.
  apply pequiv_of_pmap (pppi_compose_left g),
  apply adjointify _ (pppi_compose_left (fun a => (g a)^-1ᵉ*)),
  { intro f, apply path_pforall,
  refine !pmap_compose_ppi_pcompose^-1* @* _,
  refine pmap_compose_ppi_phomotopy_left _ (fun a => !pright_inv) @* _,
  apply pmap_compose_ppi_pid_left },
  { intro f, apply path_pforall,
  refine !pmap_compose_ppi_pcompose^-1* @* _,
  refine pmap_compose_ppi_phomotopy_left _ (fun a => !pleft_inv) @* _,
  apply pmap_compose_ppi_pid_left }
Defined.

Defined. pointed


namespace pointed

  variables {A B C : pType}

Definition pfiber.sigma_char' (f : A ->* B) :
  pfiber f <~>* psigma_gen (fun a => f a = (point _)) (point_eq f).
  pequiv_of_equiv (fiber.sigma_char f (point _)) idp

Definition fiberpt {A B : pType} {f : A ->* B} : fiber f (point _).
  fiber.mk (point _) (point_eq f)

Definition psigma_fiber_pequiv {A B : pType} (f : A ->* B) :
  psigma_gen (fiber f) fiberpt <~>* A.
  pequiv_of_equiv (sigma_fiber_equiv f) idp

Definition ppMap.sigma_char (A B : pType) :
  ppMap A B <~>* @psigma_gen (A ->ᵘ* B) (fun f => f (point _) = (point _)) idp.
  pequiv_of_equiv !pmap.sigma_char idp

Definition pppi.sigma_char (B : A -> pType) :
  (ppforall (a : A), B a) <~>* @psigma_gen (forall ᵘ*a, B a) (fun f => f (point _) = (point _)) idp.
  proof pequiv_of_equiv !ppi.sigma_char idp qed

Definition pppi_sigma_char_natural_bottom {B B' : A -> pType} (f : forall a, B a ->* B' a) :
  @psigma_gen (forall ᵘ*a, B a) (fun g => g (point _) = (point _)) idp ->* @psigma_gen (forall ᵘ*a, B' a) (fun g => g (point _) = (point _)) idp.
  psigma_gen_functor
  (pupi_functor_right f)
  (fun g p => ap (f (point _)) p @ point_eq (f (point _)))
Proof.
  apply eq_pathover_constant_right, apply square_of_eq,
  esimp, exact (concat_1p _) @ !apd10_eq_of_homotopy^-1 @ !ap_eq_apd10^-1,
Defined.

Definition pppi_sigma_char_natural {B B' : A -> pType} (f : forall a, B a ->* B' a) :
  psquare (pppi_compose_left f) (pppi_sigma_char_natural_bottom f)
  (pppi.sigma_char B) (pppi.sigma_char B').
Proof.
  fapply Build_pHomotopy,
  { intro g, reflexivity },
  { refine (concat_1p _) @ (concat_1p _) @ _,
  fapply sigma_eq2,
  { refine !sigma_eq_pr1 @ _ @ !ap_sigma_pr1^-1,
  apply inj !eq_equiv_homotopy,
  refine !apd10_eq_of_homotopy_fn @ _ @ !apd10_to_fun_path_pforall ,
  apply eq_of_homotopy, intro a, reflexivity },
  { exact sorry } }
Defined.

  open sigma.ops

Definition psigma_gen_pi_pequiv_pupi_psigma_gen {A : pType} {B : A -> pType}
  (C : forall a, B a -> Type) (c : forall a, C a (point _)) :
  @psigma_gen (forall ᵘ*a, B a) (fun f => forall a, C a (f a)) c <~>* forall ᵘ*a, psigma_gen (C a) (c a).
  pequiv_of_equiv sigma_pi_equiv_pi_sigma idp

Definition pupi_psigma_gen_pequiv_psigma_gen_pi {A : pType} {B : A -> pType}
  (C : forall a, B a -> Type) (c : forall a, C a (point _)) :
  (forall ᵘ*a, psigma_gen (C a) (c a)) <~>* @psigma_gen (forall ᵘ*a, B a) (fun f => forall a, C a (f a)) c.
  pequiv_of_equiv sigma_pi_equiv_pi_sigma^-1ᵉ idp

Definition psigma_gen_assoc {A : pType} {B : A -> Type} (C : forall a, B a -> Type)
  (b₀ : B (point _)) (c₀ : C (point _) b₀) :
  psigma_gen (fun a => Σb, C a b) ⟨b₀, c₀⟩ <~>* @psigma_gen (psigma_gen B b₀) (fun v => C v.1 v.2) c₀.
  pequiv_of_equiv !sigma_assoc_equiv' idp

Definition psigma_gen_swap {A : pType} {B B' : A -> Type}
  (C : forall (a), B a -> B' a -> Type) (b₀ : B (point _)) (b₀' : B' (point _)) (c₀ : C b₀ b₀') :
  @psigma_gen (psigma_gen B  b₀ ) (fun v => Σb', C v.2 b') ⟨b₀', c₀⟩ <~>*
  @psigma_gen (psigma_gen B' b₀') (fun v => Σb , C b  v.2) ⟨b₀ , c₀⟩.
  !psigma_gen_assoc^-1ᵉ* @e* psigma_gen_pequiv_psigma_gen_right (fun a => !sigma_comm_equiv) idp @e*
  !psigma_gen_assoc

Definition ppi_psigma.{u v w} {A : pType.{u}} {B : A -> pType.{v}} (C : forall a, B a -> Type.{w})
  (c : forall a, C a (point _)) : (ppforall (a : A), (psigma_gen (C a) (c a))) <~>*
  psigma_gen (fun (f : ppforall , B a), ppi (fun a => C a (f a))
  (transport (C (point _)) (point_eq f)^-1 (c (point _)))) (ppi_const _).
  proof
  calc (ppforall (a : A), psigma_gen (C a) (c a))
  <~>* @psigma_gen (forall ᵘ*a, psigma_gen (C a) (c a)) (fun f => f (point _) = (point _)) idp : pppi.sigma_char
  ... <~>* @psigma_gen (@psigma_gen (forall ᵘ*a, B a) (fun f => forall a, C a (f a)) c)
  (fun v => Σ(p : v.1 (point _) = (point _)), v.2 (point _) =[p] c (point _)) ⟨idp, idpo⟩ :
  by exact psigma_gen_pequiv_psigma_gen (pupi_psigma_gen_pequiv_psigma_gen_pi C c)
  (fun f => sigma_eq_equiv _ _) idpo
  ... <~>* @psigma_gen (@psigma_gen (forall ᵘ*a, B a) (fun f => f (point _) = (point _)) idp)
  (fun v => Σ(g : forall a, C a (v.1 a)), g (point _) =[v.2] c (point _)) ⟨c, idpo⟩ :
  by apply psigma_gen_swap
  ... <~>* psigma_gen (fun (f : ppforall , B a), ppi (fun a => C a (f a))
  (transport (C (point _)) (point_eq f)^-1 (c (point _))))
  (ppi_const _) :
  by exact (psigma_gen_pequiv_psigma_gen (pppi.sigma_char B)
  (fun f => !ppi.sigma_char @e sigma_equiv_sigma_right (fun g => !pathover_equiv_eq_tr^-1ᵉ))
  idpo)^-1ᵉ*
  qed

Definition ppMap_psigma {A B : pType} (C : B -> Type) (c : C (point _)) :
  ppMap A (psigma_gen C c) <~>*
  psigma_gen (fun (f : ppMap A B) => ppi (C o f) (transport C (point_eq f)^-1 c))
  (ppi_const _).
  !pppi_pequiv_ppMap^-1ᵉ* @e* !ppi_psigma @e*
  sorry

Definition pfiber_pppi_compose_left {B C : A -> pType} (f : forall a, B a ->* C a) :
  pfiber (pppi_compose_left f) <~>* ppforall (a : A), pfiber (f a).
  calc
  pfiber (pppi_compose_left f) <~>*
  psigma_gen (fun (g : ppforall , B a), pmap_compose_ppi f g = ppi_const C)
  proof (path_pforall (pmap_compose_ppi_ppi_const f)) qed :
  by exact !pfiber.sigma_char'
  ... <~>* psigma_gen (fun (g : ppforall , B a), pmap_compose_ppi f g ==* ppi_const C)
  proof (pmap_compose_ppi_ppi_const f) qed :
  by exact psigma_gen_pequiv_psigma_gen_right (fun a => !ppi_eq_equiv)
  !phomotopy_path_of_phomotopy
  ... <~>* @psigma_gen (ppforall (a : A), B a) (fun (g : ppforall , B a), ppi (fun a => f a (g a) = (point _))
  (transport (fun b => f (point _) b = (point _)) (point_eq g)^-1 (point_eq (f (point _)))))
  (ppi_const _) :
Proof.
  refine psigma_gen_pequiv_psigma_gen_right
  (fun g => ppi_equiv_ppi_basepoint (_ @ !eq_transport_Fl^-1)) _,
  intro g, refine (concat_p1 _) @ _, apply whisker_right,
  exact ap02 (f (point _)) !inv_inv^-1 @ !ap_inv,
  apply path_pforall, fapply Build_pHomotopy,
  intro x, reflexivity,
  refine (concat_1p _) @ _, symmetry, refine !ap_id ◾ (concat_1p _) @ _, apply con.right_inv
Defined.
  ... <~>* ppforall (a : A), (psigma_gen (fun b => f a b = (point _)) (point_eq (f a))) :
  by exact (ppi_psigma _ _)^-1ᵉ*
  ... <~>* ppforall (a : A), pfiber (f a) : by exact ppi_pequiv_right (fun a => !pfiber.sigma_char'^-1ᵉ*)

  (* TODO: proof the following as a special case of pfiber_pppi_compose_left *)
Definition pfiber_ppcompose_left (f : B ->* C) :
  pfiber (@ppcompose_left A B C f) <~>* ppMap A (pfiber f).
  calc
  pfiber (@ppcompose_left A B C f) <~>*
  psigma_gen (fun (g : ppMap A B) => f o* g = pconst A C)
  proof (path_pforall (pcompose_pconst f)) qed :
  by exact !pfiber.sigma_char'
  ... <~>* psigma_gen (fun (g : ppMap A B) => f o* g ==* pconst A C) proof (pcompose_pconst f) qed :
  by exact psigma_gen_pequiv_psigma_gen_right (fun a => !pmap_eq_equiv)
  !phomotopy_path_of_phomotopy
  ... <~>* psigma_gen (fun (g : ppMap A B) => ppi (fun a => f (g a) = (point _))
  (transport (fun b => f b = (point _)) (point_eq g)^-1 (point_eq f)))
  (ppi_const _) :
Proof.
  refine psigma_gen_pequiv_psigma_gen_right
  (fun g => ppi_equiv_ppi_basepoint (_ @ !eq_transport_Fl^-1)) _,
  intro g, refine (concat_p1 _) @ _, apply whisker_right,
  exact ap02 f !inv_inv^-1 @ !ap_inv,
  apply path_pforall, fapply Build_pHomotopy,
  intro x, reflexivity,
  refine (concat_1p _) @ _, symmetry, refine !ap_id ◾ (concat_1p _) @ _, apply con.right_inv
Defined.
  ... <~>* ppMap A (psigma_gen (fun b => f b = (point _)) (point_eq f)) :
  by exact (ppMap_psigma _ _)^-1ᵉ*
  ... <~>* ppMap A (pfiber f) : by exact ppMap_pequiv_ppMap_right !pfiber.sigma_char'^-1ᵉ*


Definition ppi_add_point_over {A : Type} (B : A -> pType) :
  (ppforall a, add_point_over B a) <~> forall a, B a.
Proof.
  fapply equiv.MK,
  { intro f a, exact f (some a) },
  { intro f, fconstructor,
  intro a, cases a, exact (point _), exact f a,
  reflexivity },
  { intro f, reflexivity },
  { intro f, cases f with f p, apply path_pforall, fapply Build_pHomotopy,
  { intro a, cases a, exact p^-1, reflexivity },
  { exact con.left_inv p }},
Defined.

Definition pppi_add_point_over {A : Type} (B : A -> pType) :
  (ppforall a, add_point_over B a) <~>* forall ᵘ*a, B a.
  pequiv_of_equiv (ppi_add_point_over B) idp

Definition ppMap_add_point {A : Type} (B : pType) :
  ppMap A₊ B <~>* A ->ᵘ* B.
  pequiv_of_equiv (pmap_equiv_left A B) idp

  (* There are some lemma's needed to prove the naturality of the equivalence
  loops (ppforall a, B a) <~>* ppforall (a : A), loops (B a) *)
Definition ppi_eq_equiv_natural_gen_lem {B C : A -> Type} {b₀ : B (point _)} {c₀ : C (point _)}
  {f : forall (a : A), B a -> C a} {f₀ : f (point _) b₀ = c₀} {k : ppi B b₀} {k' : ppi C c₀}
  (p : ppi_functor_right f f₀ k ==* k') :
  ap1_gen (f (point _)) (p (point _)) f₀ (point_eq k) = point_eq k'.
Proof.
  symmetry,
  refine _ @ (concat_pp_p _ _ _)^-1,
  exact eq_inv_con_of_con_eq (point_htpy p),
Defined.

Definition ppi_eq_equiv_natural_gen_lem2 {B C : A -> Type} {b₀ : B (point _)} {c₀ : C (point _)}
  {f : forall (a : A), B a -> C a} {f₀ : f (point _) b₀ = c₀} {k l : ppi B b₀}
  {k' l' : ppi C c₀} (p : ppi_functor_right f f₀ k ==* k')
  (q : ppi_functor_right f f₀ l ==* l') :
  ap1_gen (f (point _)) (p (point _)) (q (point _)) (point_eq k @ (point_eq l)^-1) =
  point_eq k' @ (point_eq l')^-1.
  (ap1_gen_con (f (point _)) _ f₀ _ _ _ @ (ppi_eq_equiv_natural_gen_lem p) ◾
  (!ap1_gen_inv @ (ppi_eq_equiv_natural_gen_lem q)⁻²))

Definition ppi_eq_equiv_natural_gen {B C : A -> Type} {b₀ : B (point _)} {c₀ : C (point _)}
  {f : forall (a : A), B a -> C a} {f₀ : f (point _) b₀ = c₀} {k l : ppi B b₀}
  {k' l' : ppi C c₀} (p : ppi_functor_right f f₀ k ==* k')
  (q : ppi_functor_right f f₀ l ==* l') :
  hsquare (ap1_gen (ppi_functor_right f f₀) (path_pforall p) (path_pforall q))
  (ppi_functor_right (fun a => ap1_gen (f a) (p a) (q a))
  (ppi_eq_equiv_natural_gen_lem2 p q))
  phomotopy_path
  phomotopy_path.
Proof.
  intro r, induction r,
  induction f₀,
  induction k with k k₀,
  induction k₀,
  refine idp @ _,
  revert l' q, refine phomotopy_rec_idp' _ _,
  revert k' p, refine phomotopy_rec_idp' _ _,
  reflexivity
Defined.

Definition ppi_eq_equiv_natural_gen_refl {B C : A -> Type}
  {f : forall (a : A), B a -> C a} {k : forall a, B a} :
  ppi_eq_equiv_natural_gen (reflexivity (ppi_functor_right f idp (ppi.mk k idp)))
  (reflexivity (ppi_functor_right f idp (ppi.mk k idp))) idp =
  ap phomotopy_path !ap1_gen_idp.
Proof.
  refine (concat_1p _) @ _,
  refine !phomotopy_rec_idp'_refl @ _,
  refine ap (transport _ _) !phomotopy_rec_idp'_refl @ _,
  refine !tr_diag_eq_tr_tr^-1 @ _,
  refine !eq_transport_Fl @ _,
  refine !ap_inv⁻² @ !inv_inv @ !ap_compose @ ap02 _ _,
  exact !ap1_gen_idp_eq^-1
Defined.

Definition loop_pppi_pequiv {A : pType} (B : A -> pType) :
  loops (ppforall a, B a) <~>* ppforall (a : A), loops (B a).
  pequiv_of_equiv !ppi_eq_equiv idp

Definition loop_pppi_pequiv_natural_right {A : pType} {X Y : A -> pType}
  (f :  forall (a : A), X a ->* Y a) :
  psquare (loop_pppi_pequiv X)
  (loop_pppi_pequiv Y)
  (Ω-> (pppi_compose_left f))
  (pppi_compose_left (fun a => Ω-> (f a))).
Proof.
  apply ptranspose,
  revert Y f, refine fiberwise_pointed_map_rec _ _, intro Y f,
  fapply Build_pHomotopy,
  { exact ppi_eq_equiv_natural_gen (pmap_compose_ppi_ppi_const (fun a => pmap_of_map (f a) (point _)))
  (pmap_compose_ppi_ppi_const (fun a => pmap_of_map (f a) (point _))) },
  { exact !ppi_eq_equiv_natural_gen_refl ◾ ((concat_1p _) @ !path_pforall_refl) }
Defined.

Definition loop_pppi_pequiv_natural_left {A B : pType} {X : A -> pType} (f : B ->* A) :
  psquare (loop_pppi_pequiv X)
  (loop_pppi_pequiv (X o f))
  (Ω-> (pppi_compose_right f))
  (pppi_compose_right f).
Proof.
  exact sorry
Defined.

Definition loopn_pppi_pequiv (n : ℕ) {A : pType} (B : A -> pType) :
  Ω[n] (ppforall a, B a) <~>* ppforall (a : A), Ω[n] (B a).
Proof.
  induction n with n IH,
  { reflexivity },
  { refine loop_pequiv_loop IH @e* loop_pppi_pequiv (fun a => Ω[n] (B a)) }
Defined.

Definition loop_ppMap_pequiv (A B : pType) : loops (A ->** B) <~>* A ->** loops B.
  !loop_pppi_pequiv

Definition loop_ppMap_pequiv_natural_right (A : pType) {X Y : pType} (f :  X ->* Y) :
  psquare (loop_ppMap_pequiv A X)
  (loop_ppMap_pequiv A Y)
  (Ω-> (ppcompose_left f))
  (ppcompose_left (Ω-> f)).
Proof.
  exact loop_pppi_pequiv_natural_right (fun a => f)
Defined.

Definition loop_ppMap_pequiv_natural_left {A B : pType} (X : pType) (f :  A ->* B) :
  psquare (loop_ppMap_pequiv B X)
  (loop_ppMap_pequiv A X)
  (Ω-> (ppcompose_right f))
  (ppcompose_right f).
Proof.
  refine Ω⇒ !pppi_compose_right_phomotopy^-1* @ph* _ @hp* !pppi_compose_right_phomotopy^-1*,
  exact loop_pppi_pequiv_natural_left f
Defined.

Definition loopn_ppMap_pequiv (n : ℕ) (A B : pType) : Ω[n] (A ->** B) <~>* A ->** Ω[n] B.
  !loopn_pppi_pequiv

Definition pfunext {A : pType} (B : A -> pType) :
  (ppforall (a : A), loops (B a)) <~>* loops (ppforall a, B a).
  (loop_pppi_pequiv B)^-1ᵉ*

Definition deloopable_pppi [instance] {A : pType} (B : A -> pType) [forall a, deloopable (B a)] :
  deloopable (ppforall a, B a).
deloopable.mk (ppforall a, deloop (B a))
  (loop_pppi_pequiv (fun a => deloop (B a)) @e* ppi_pequiv_right (fun a => deloop_pequiv (B a)))

Definition deloopable_ppMap [instance] (A B : pType) [deloopable B] :
  deloopable (A ->** B).
deloopable_pppi (fun a => B)


(* below is an alternate proof strategy for the naturality of loop_pppi_pequiv_natural,
  where we define loop_pppi_pequiv as composite of pointed equivalences, and proved the
  naturality individually. That turned out to be harder.
*)

(*Definition loop_pppi_pequiv2 {A : pType} (B : A -> pType) : loops (ppforall a, B a) <~>* ppforall (a : A), loops (B a).
Proof.
  refine loop_pequiv_loop (pppi.sigma_char B) @e* _,
  refine !loop_psigma_gen @e* _,
  transitivity @psigma_gen (forall ᵘ*a, loops (B a)) (fun f => f (point _) = idp) idp,
  exact psigma_gen_pequiv_psigma_gen
  (loop_pupi B) (fun p => eq_pathover_equiv_Fl p idp idp @e
  equiv_eq_closed_right _ (whisker_right _ (ap_eq_apd10 p _)) @e !eq_equiv_eq_symm) idpo,
  exact (pppi.sigma_char (loops o B))^-1ᵉ*
Defined.

Definition loop_pppi_pequiv_natural2 {A : pType} {X Y : A -> pType} (f :  forall (a : A), X a ->* Y a) :
  psquare
  (Ω-> (pppi_compose_left f))
  (pppi_compose_left (fun a => Ω-> (f a)))
  (loop_pppi_pequiv2 X)
  (loop_pppi_pequiv2 Y).
Proof.
  refine ap1_psquare (pppi_sigma_char_natural f) @v* _,
  refine !loop_psigma_gen_natural @v* _,
  refine _ @v* (pppi_sigma_char_natural (fun a => Ω-> (f a)))^-1ᵛ*,
  fapply psigma_gen_functor_psquare =>
  { apply loop_pupi_natural },
  { intro p q, exact sorry },
  { exact sorry }
Defined.*)

Defined. pointed open pointed

open is_trunc is_conn
namespace is_conn
  section

  (* todo: reorder arguments and make some implicit *)
  variables (A : pType) (n : ℕ₋₂) (H : is_conn (n.+1) A)
  include H

Definition is_contr_ppi_match (P : A -> pType) (H2 : forall a, is_trunc (n.+1) (P a))
  : is_contr (ppforall (a : A), P a).
Proof.
  apply is_contr.mk (point _),
  intro f, induction f with f p,
  apply path_pforall, fapply Build_pHomotopy,
  { apply is_conn.elim n, exact p^-1 },
  { krewrite (is_conn.elim_β n), apply con.left_inv }
Defined.


Definition is_trunc_ppi_of_is_conn (k l : ℕ₋₂) (H2 : l ≤ n.+1+2+k)
  (P : A -> pType) (H3 : forall a, is_trunc l (P a)) :
  is_trunc k.+1 (ppforall (a : A), P a).
Proof.
  have H4 : forall a, is_trunc (n.+1+2+k) (P a), from fun a => is_trunc_of_le (P a) H2 _,
  clear H2 H3, revert P H4,
  induction k with k IH: intro P H4,
  { apply is_prop_of_imp_is_contr, intro f,
  apply is_contr_ppi_match A n H P H4 },
  { apply is_trunc_succ_of_is_trunc_loop
  (trunc_index.succ_le_succ (trunc_index.minus_two_le k)),
  intro f,
  apply @is_trunc_equiv_closed_rev _ _ k.+1 (ppi_loop_equiv f),
  apply IH, intro a,
  apply is_trunc_loop, apply H4 }
Defined.

Definition is_trunc_pmap_of_is_conn (k l : ℕ₋₂) (B : pType) (H2 : l ≤ n.+1+2+k)
  (H3 : is_trunc l B) : is_trunc k.+1 (A ->* B).
  is_trunc_ppi_of_is_conn A n H k l H2 (fun a => B) _

Defined.

  open trunc_index algebra nat
Definition is_trunc_ppi_of_is_conn_nat
  (A : pType) (n : ℕ) (H : is_conn (n.-1) A) (k l : ℕ) (H2 : l ≤ n + k)
  (P : A -> pType) (H3 : forall a, is_trunc l (P a)) :
  is_trunc k (ppforall (a : A), P a).
Proof.
  refine is_trunc_ppi_of_is_conn A (n.-2) H (k.-1) l _ P H3,
  refine le.trans (of_nat_le_of_nat H2) (le_of_eq !sub_one_add_plus_two_sub_one^-1)
Defined.

Definition is_trunc_pmap_of_is_conn_nat (A : pType) (n : ℕ) (H : is_conn (n.-1) A) (k l : ℕ)
  (B : pType) (H2 : l ≤ n + k) (H3 : is_trunc l B) : is_trunc k (A ->* B).
  is_trunc_ppi_of_is_conn_nat A n H k l H2 (fun a => B) _

Definition is_trunc_ppi (A : pType) (n k : ℕ₋₂) (H : n ≤ k) (P : A -> pType)
  (H2 : forall a, is_trunc n (P a)) : is_trunc k (ppforall (a : A), P a).
Proof.
  cases k with k,
  { apply is_contr_of_merely_prop,
  { exact @is_trunc_ppi_of_is_conn A -2 (is_conn_minus_one A (tr (point _))) -2 _
  (trunc_index.le.step H) P H2 },
  { exact tr (point _) } },
  { assert K : n ≤ -1 +2+ k,
  { rewrite (trunc_index.add_plus_two_comm -1 k), exact H },
  { exact @is_trunc_ppi_of_is_conn A -2 (is_conn_minus_one A (tr (point _))) k _ K P H2 } }
Defined.

Defined. is_conn


(* TODO: move, these facts use some of these pointed properties *)

namespace trunc

lemma pmap_ptrunc_pequiv_natural (n : ℕ₋₂) {A A' B B' : pType}
  [H : is_trunc n B] [H : is_trunc n B'] (f : A' ->* A) (g : B ->* B') :
  psquare (pmap_ptrunc_pequiv n A B) (pmap_ptrunc_pequiv n A' B')
  (ppcompose_left g o* ppcompose_right (ptrunc_functor n f))
  (ppcompose_left g o* ppcompose_right f).
Proof.
  refine _ @v* _, exact pmap_ptrunc_pequiv n A' B,
  { fapply Build_pHomotopy,
  { intro h, apply path_pforall,
  exact !passoc @* pwhisker_left h (ptr_natural n f)^-1* @* !passoc^-1* },
  { xrewrite [▸*, +pcompose_right_path_pforall, -+path_pforall_trans],
  apply ap path_pforall,
  refine !trans_assoc @ idp ◾** (!trans_assoc^-1 @ (eq_bot_of_phsquare (phtranspose
  (passoc_pconst_left (ptrunc_functor n f) (ptr n A'))))^-1) @ _ =>
  refine !trans_assoc @ idp ◾** !pconst_pcompose_phomotopy @ _,
  apply passoc_pconst_left }},
  { fapply Build_pHomotopy,
  { intro h, apply path_pforall, exact !passoc^-1* },
  { xrewrite [▸*, pcompose_right_path_pforall, pcompose_left_path_pforall,
  -+path_pforall_trans],
  apply ap path_pforall, apply symm_trans_eq_of_eq_trans, symmetry,
  apply passoc_pconst_middle }}
Defined.
Defined. trunc
