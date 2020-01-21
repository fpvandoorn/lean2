(*
Copyright (c) 2018 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
*)

import .pointed_pi

open eq pointed equiv sigma is_equiv trunc option pi function fiber sigma.ops

namespace pointed

section bpmap
(* binary pointed maps *)
structure bpmap (A B C : pType) : Type.
  (f : A -> B ->* C)
  (q : forall b, f (point _) b = (point _))
  (r : q (point _) = point_eq (f (point _)))


variables {A B C D A' B' C' : pType} {f f' : bpmap A B C}
Definition point_eq1 (f : bpmap A B C) (b : B) : f (point _) b = (point _).
bpmap.q f b

Definition point_eq2 (f : bpmap A B C) (a : A) : f a (point _) = (point _).
point_eq (f a)

Definition point_eqpt (f : bpmap A B C) : point_eq1 f (point _) = point_eq2 f (point _).
bpmap.r f

Definition bpconst (A B C : pType) : bpmap A B C.
bBuild_pMap (fun a => pconst B C) (fun b => idp) idp

Definition bppMap (A B C : pType) : pType.
pointed.MK (bpmap A B C) (bpconst A B C)

Definition pmap_of_bpmap (f : bppMap A B C) : ppMap A (ppMap B C).
Proof.
  fapply Build_pMap,
  { intro a, exact Build_pMap (f a) (point_eq2 f a) },
  { exact path_pforall (Build_pHomotopy (point_eq1 f) (point_eqpt f)) }
Defined.

Definition bpmap_of_pmap (f : ppMap A (ppMap B C)) : bppMap A B C.
Proof.
  apply bBuild_pMap (fun a => f a) (ap010 pmap.to_fun (point_eq f)) =>
  exact point_eq (phomotopy_path (point_eq f))
Defined.

protectedDefinition bpmap.sigma_char (A B C : pType) :
  bpmap A B C <~> Σ(f : A -> B ->* C) (q : forall b, f (point _) b = (point _)), q (point _) = point_eq (f (point _)).
Proof.
  fapply equiv.MK,
  { intro f, exact ⟨f, point_eq1 f, point_eqpt f⟩ },
  { intro fqr, exact bBuild_pMap fqr.1 fqr.2.1 fqr.2.2 },
  { intro fqr, induction fqr with f qr, induction qr with q r, reflexivity },
  { intro f, induction f, reflexivity }
Defined.

Definition point_htpy_square {f g : A ->* B} (h : f ==* g) :
  square (point_eq f) (point_eq g) (h (point _)) idp.
square_of_eq (point_htpy h)^-1

Definition bpmap_eq_equiv (f f' : bpmap A B C):
  f = f' <~> Σ(h : forall a, f a ==* f' a) (q : forall b, square (point_eq1 f b) (point_eq1 f' b) (h (point _) b) idp), cube (vdeg_square (point_eqpt f)) (vdeg_square (point_eqpt f'))
  vrfl ids
  (q (point _)) (point_htpy_square (h (point _))).
Proof.
  refine eq_equiv_fn_eq (bpmap.sigma_char A B C) f f' @e _,
  refine !sigma_eq_equiv @e _, esimp,
  refine sigma_equiv_sigma (!eq_equiv_homotopy @e pi_equiv_pi_right (fun a => !pmap_eq_equiv)) _,
  intro h, exact sorry
Defined.

Definition bpmap_eq (h : forall a, f a ==* f' a)
  (q : forall b, square (point_eq1 f b) (point_eq1 f' b) (h (point _) b) idp)
  (r : cube (vdeg_square (point_eqpt f)) (vdeg_square (point_eqpt f'))
  vrfl ids
  (q (point _)) (point_htpy_square (h (point _)))) : f = f'.
(bpmap_eq_equiv f f')^-1ᵉ ⟨h, q, r⟩

Definition pmap_equiv_bpmap (A B C : pType) : pmap A (ppMap B C) <~> bpmap A B C.
Proof.
  refine !pmap.sigma_char @e _ @e !bpmap.sigma_char^-1ᵉ,
  refine sigma_equiv_sigma_right (fun f => pmap_eq_equiv (f (point _)) !pconst) @e _,
  refine sigma_equiv_sigma_right (fun f => !phomotopy.sigma_char)
Defined.

Definition pmap_equiv_bpmap' (A B C : pType) : pmap A (ppMap B C) <~> bpmap A B C.
Proof.
  refine equiv_change_fun (pmap_equiv_bpmap A B C) _ =>
  exact bpmap_of_pmap, intro f, reflexivity
Defined.

Definition ppMap_pequiv_bppMap (A B C : pType) :
  ppMap A (ppMap B C) <~>* bppMap A B C.
pequiv_of_equiv (pmap_equiv_bpmap' A B C) idp

Definition bpmap_functor (f : A' ->* A) (g : B' ->* B) (h : C ->* C')
  (k : bpmap A B C) : bpmap A' B' C'.
Proof.
  fapply bBuild_pMap (fun a' => h o* k (f a') o* g),
  { intro b', refine ap h _ @ point_eq h,
  exact ap010 (fun a b => k a b) (point_eq f) (g b') @ point_eq1 k (g b') },
  { apply whisker_right, apply ap02 h, esimp,
  induction A with A a₀, induction B with B b₀, induction f with f f₀, induction g with g g₀,
  esimp at *, induction f₀, induction g₀, esimp, apply whisker_left, exact point_eqpt k },
Defined.

Definition bppMap_functor (f : A' ->* A) (g : B' ->* B) (h : C ->* C') :
  bppMap A B C ->* bppMap A' B' C'.
Proof.
  apply Build_pMap (bpmap_functor f g h) =>
  induction A with A a₀, induction B with B b₀, induction C' with C' c₀',
  induction f with f f₀, induction g with g g₀, induction h with h h₀, esimp at *,
  induction f₀, induction g₀, induction h₀,
  reflexivity
Defined.

Definition ppcompose_left' (g : B ->* C) : ppMap A B ->* ppMap A C.
  Build_pMap (pcompose g)
Proof. induction C with C c₀, induction g with g g₀, esimp at *, induction g₀, reflexivity end

Definition ppcompose_right' (f : A ->* B) : ppMap B C ->* ppMap A C.
  Build_pMap (fun g => g o* f)
Proof. induction B with B b₀, induction f with f f₀, esimp at *, induction f₀, reflexivity end

Definition ppMap_pequiv_bppMap_natural (f : A' ->* A) (g : B' ->* B) (h : C ->* C') :
  psquare (ppMap_pequiv_bppMap A B C) (ppMap_pequiv_bppMap A' B' C')
  (ppcompose_right' f o* ppcompose_left' (ppcompose_right' g o* ppcompose_left' h))
  (bppMap_functor f g h).
Proof.
  induction A with A a₀, induction B with B b₀, induction C' with C' c₀',
  induction f with f f₀, induction g with g g₀, induction h with h h₀, esimp at *,
  induction f₀, induction g₀, induction h₀,
  fapply Build_pHomotopy,
  { intro k, fapply bpmap_eq,
  { intro a, exact !passoc^-1* },
  { intro b, apply vdeg_square, esimp,
  refine ap02 _ (concat_1p _) @ _ @ (ap (fun x => ap010 pmap.to_fun x b) (concat_1p _))^-1ᵖ =>
  refine ap02 _ !ap_eq_ap010^-1 @ !ap_compose' @ !ap_compose @ !ap_eq_ap010 },
  { exact sorry }},
  { exact sorry }
Defined.

(* maybe this is useful for pointed naturality in C? *)
Definition ppMap_pequiv_bppMap_natural_right (h : C ->* C') :
  psquare (ppMap_pequiv_bppMap A B C) (ppMap_pequiv_bppMap A B C')
  (ppcompose_left' (ppcompose_left' h))
  (bppMap_functor !pid !pid h).
Proof.
  induction A with A a₀, induction B with B b₀, induction C' with C' c₀',
  induction h with h h₀, esimp at *, induction h₀,
  fapply Build_pHomotopy,
  { intro k, fapply bpmap_eq,
  { intro a, exact pwhisker_left _ !pcompose_pid },
  { intro b, apply vdeg_square, esimp,
  refine ap02 _ (concat_1p _) @ _,
  refine ap02 _ !ap_eq_ap010^-1 @ !ap_compose' @ !ap_compose @ !ap_eq_ap010 },
  { exact sorry }},
  { exact sorry }
Defined.
Defined. bpmap

(* fiberwise pointed maps *)
structure dbpmap {A : pType} (B C : A -> pType) : Type.
  (f : forall a, B a ->* C a)
  (q : forall b, f (point _) b = (point _))
  (r : q (point _) = point_eq (f (point _)))


variables {A A' : pType} {B C : A -> pType} {B' C' : A' -> pType} {f f' : dbpmap B C}
Definition point_eqd1 (f : dbpmap B C) (b : B (point _)) : f (point _) b = (point _).
dbpmap.q f b

Definition point_eqd2 (f : dbpmap B C) (a : A) : f a (point _) = (point _).
point_eq (f a)

Definition respect_dptpt (f : dbpmap B C) : point_eqd1 f (point _) = point_eqd2 f (point _).
dbpmap.r f

Definition dbpconst (B C : A -> pType) : dbpmap B C.
dbBuild_pMap (fun a => pconst (B a) (C a)) (fun b => idp) idp

Definition dbppMap (B C : A -> pType) : pType.
pointed.MK (dbpmap B C) (dbpconst B C)

Definition ppi_of_dbpmap (f : dbppMap B C) : ppforall a, B a ->** C a.
Proof.
  fapply ppi.mk,
  { intro a, exact Build_pMap (f a) (point_eqd2 f a) },
  { exact path_pforall (Build_pHomotopy (point_eqd1 f) (respect_dptpt f)) }
Defined.

Definition dbpmap_of_ppi (f : ppforall a, B a ->** C a) : dbppMap B C.
Proof.
  apply dbBuild_pMap (fun a => f a) (ap010 pmap.to_fun (point_eq f)) =>
  exact point_eq (phomotopy_path (point_eq f))
Defined.

protectedDefinition dbpmap.sigma_char (B C : A -> pType) :
  dbpmap B C <~> Σ(f : forall a, B a ->* C a) (q : forall b, f (point _) b = (point _)), q (point _) = point_eq (f (point _)).
Proof.
  fapply equiv.MK,
  { intro f, exact ⟨f, point_eqd1 f, respect_dptpt f⟩ },
  { intro fqr, exact dbBuild_pMap fqr.1 fqr.2.1 fqr.2.2 },
  { intro fqr, induction fqr with f qr, induction qr with q r, reflexivity },
  { intro f, induction f, reflexivity }
Defined.

Definition dbpmap_eq_equiv (f f' : dbpmap B C):
  f = f' <~> Σ(h : forall a, f a ==* f' a) (q : forall b, square (point_eqd1 f b) (point_eqd1 f' b) (h (point _) b) idp), cube (vdeg_square (respect_dptpt f)) (vdeg_square (respect_dptpt f'))
  vrfl ids
  (q (point _)) (point_htpy_square (h (point _))).
Proof.
  refine eq_equiv_fn_eq (dbpmap.sigma_char B C) f f' @e _,
  refine !sigma_eq_equiv @e _, esimp,
  refine sigma_equiv_sigma (!eq_equiv_homotopy @e pi_equiv_pi_right (fun a => !pmap_eq_equiv)) _,
  intro h, exact sorry
Defined.

Definition dbpmap_eq (h : forall a, f a ==* f' a)
  (q : forall b, square (point_eqd1 f b) (point_eqd1 f' b) (h (point _) b) idp)
  (r : cube (vdeg_square (respect_dptpt f)) (vdeg_square (respect_dptpt f'))
  vrfl ids
  (q (point _)) (point_htpy_square (h (point _)))) : f = f'.
(dbpmap_eq_equiv f f')^-1ᵉ ⟨h, q, r⟩

Definition ppi_equiv_dbpmap (B C : A -> pType) : (ppforall a, B a ->** C a) <~> dbpmap B C.
Proof.
  refine !ppi.sigma_char @e _ @e !dbpmap.sigma_char^-1ᵉ,
  refine sigma_equiv_sigma_right (fun f => pmap_eq_equiv (f (point _)) !pconst) @e _,
  refine sigma_equiv_sigma_right (fun f => !phomotopy.sigma_char)
Defined.

Definition ppi_equiv_dbpmap' (B C : A -> pType) : (ppforall a, B a ->** C a) <~> dbpmap B C.
Proof.
  refine equiv_change_fun (ppi_equiv_dbpmap B C) _ =>
  exact dbpmap_of_ppi, intro f, reflexivity
Defined.

Definition pppi_pequiv_dbppMap (B C : A -> pType) :
  (ppforall a, B a ->** C a) <~>* dbppMap B C.
pequiv_of_equiv (ppi_equiv_dbpmap' B C) idp

Definition dbpmap_functor (f : A' ->* A) (g : forall , B' a ->* B (f a)) (h : forall a, C (f a) ->* C' a)
  (k : dbpmap B C) : dbpmap B' C'.
Proof.
  fapply dbBuild_pMap (fun a' => h a' o* k (f a') o* g a'),
  { intro b', refine ap (h (point _)) _ @ point_eq (h (point _)),
  exact sorry }, --ap010 (fun a b => k a b) (point_eq f) (g (point _) b') @ point_eqd1 k (g (point _) b') },
  { exact sorry },
Defined.

Defined. pointed
