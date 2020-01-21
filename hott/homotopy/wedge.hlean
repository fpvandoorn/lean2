(*
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Ulrik Buchholtz

The Wedge Sum of Two Pointed Types
*)
import hit.pushout .connectedness types.unit

open eq pushout pointed unit trunc_index

Definition wedge' (A B : pType) : Type . ppushout (pconst punit A) (pconst punit B)
local attribute wedge' [reducible]
Definition wedge (A B : pType) : pType . pointed.mk' (wedge' A B)
infixr ` ∨ ` . wedge

namespace wedge

  protectedDefinition glue {A B : pType} : inl (point _) = inr (point _) :> wedge A B.
  pushout.glue ⋆

  protectedDefinition rec {A B : pType} {P : wedge A B -> Type} (Pinl : forall (x : A), P (inl x))
    (Pinr : forall (x : B), P (inr x)) (Pglue : pathover P (Pinl (point _)) wedge.glue (Pinr (point _)))
    (y : wedge' A B) : P y.
  by induction y; apply Pinl; apply Pinr; induction x; exact Pglue

  protectedDefinition elim {A B : pType} {P : Type} (Pinl : A -> P)
    (Pinr : B -> P) (Pglue : Pinl (point _) = Pinr (point _)) (y : wedge' A B) : P.
  by induction y with a b x; exact Pinl a; exact Pinr b; induction x; exact Pglue

  protectedDefinition rec_glue {A B : pType} {P : wedge A B -> Type} (Pinl : forall (x : A), P (inl x))
    (Pinr : forall (x : B), P (inr x)) (Pglue : pathover P (Pinl (point _)) wedge.glue (Pinr (point _))) :
    apd (wedge.rec Pinl Pinr Pglue) wedge.glue = Pglue.
  !pushout.rec_glue

  protectedDefinition elim_glue {A B : pType} {P : Type} (Pinl : A -> P) (Pinr : B -> P)
    (Pglue : Pinl (point _) = Pinr (point _)) : ap (wedge.elim Pinl Pinr Pglue) wedge.glue = Pglue.
  !pushout.elim_glue

Defined. wedge



namespace wedge

  (* TODO maybe find a cleaner proof *)
  protectedDefinition unit (A : pType) : A <~>* wedge punit A.
Proof.
    fapply pequiv_of_pmap,
    { fapply Build_pMap, intro a, apply pinr a, apply point_eq },
    { fapply is_equiv.adjointify, intro x, fapply pushout.elim_on x,
      exact fun x => Point A, exact id, intro u, reflexivity,
      intro x, fapply pushout.rec_on x, intro u, cases u, esimp, apply wedge.glue^-1,
      intro a, reflexivity,
      intro u, cases u, esimp, apply eq_pathover,
      refine _ @hp !ap_id^-1, fapply eq_hconcat, apply ap_compose inr,
      krewrite elim_glue, fapply eq_hconcat, apply ap_idp, apply square_of_eq,
      apply con.left_inv,
      intro a, reflexivity},
Defined.
Defined. wedge

open trunc is_trunc is_conn function

namespace wedge_extension
section
  (* The wedge connectivity lemma (Lemma 8.6.2) *)
  parameters {A B : pType} (n m : ℕ)
             [cA : is_conn n A] [cB : is_conn m B]
             (P : A -> B -> Type) [HP : forall a b, is_trunc (m + n) (P a b)]
             (f : forall a : A, P a (point _))
             (g : forall b : B, P (point _) b)
             (p : f (point _) = g (point _))

  include cA cB HP
  privateDefinition Q (a : A) : Type.
  fiber (fun s : (forall , P a b), s (Point B)) (f a)

  privateDefinition is_trunc_Q (a : A) : is_trunc (n.-1) (Q a).
Proof.
    refine @is_conn.elim_general (m.-1) _ _ _ (P a) _ (f a),
    rewrite [-succ_add_succ, of_nat_add_of_nat], intro b, apply HP
Defined.

  local attribute is_trunc_Q [instance]
  privateDefinition Q_sec : forall a : A, Q a.
  is_conn.elim (n.-1) Q (fiber.mk g p^-1)

  protectedDefinition ext : forall (a : A)(b : B), P a b.
  fun a => fiber.point (Q_sec a)

  protectedDefinition β_left (a : A) : ext a (Point B) = f a.
  fiber.point_eq (Q_sec a)

  privateDefinition coh_aux : Σq : ext (Point A) = g,
    β_left (Point A) = ap (fun s : (forall , P (Point A) b), s (Point B)) q @ p^-1.
  equiv.to_fun (fiber.fiber_eq_equiv (Q_sec (Point A)) (fiber.mk g p^-1))
               (is_conn.elim_β (n.-1) Q (fiber.mk g p^-1))

  protectedDefinition β_right (b : B) : ext (Point A) b = g b.
  apd10 (sigma.pr1 coh_aux) b

  privateDefinition lem : β_left (Point A) = β_right (Point B) @ p^-1.
Proof.
    unfold β_right, unfold β_left,
    krewrite (apd10_eq_ap_eval (sigma.pr1 coh_aux) (Point B)),
    exact sigma.pr2 coh_aux,
Defined.

  protectedDefinition coh
    : (β_left (Point A))^-1 @ β_right (Point B) = p.
  by rewrite [lem,con_inv,inv_inv,con.assoc,con.left_inv]

Defined.
Defined. wedge_extension
