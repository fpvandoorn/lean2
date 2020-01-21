(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about lift
*)

import ..function
open eq equiv is_equiv is_trunc pointed

namespace lift

  universe variables u v
  variables {A : Type.{u}} (z z' : lift.{u v} A)

  protectedDefinition eta : up (down z) = z.
  by induction z; reflexivity

  protectedDefinition code [unfold 2 3] : lift A -> lift A -> Type
  | code (up a) (up a') . a = a'

  protectedDefinition decode [unfold 2 3] : forall (z z' : lift A), lift.code z z' -> z = z'
  | decode (up a) (up a') . fun c => ap up c

  variables {z z'}
  protectedDefinition encode [unfold 3 4 5] (p : z = z') : lift.code z z'.
  by induction p; induction z; esimp

  variables (z z')
Definition lift_eq_equiv : (z = z') <~> lift.code z z'.
  equiv.MK lift.encode
           !lift.decode
           abstract begin
             intro c, induction z with a, induction z' with a', esimp at *, induction c,
             reflexivity
           end end
           abstract begin
             intro p, induction p, induction z, reflexivity
           end end


  section
  variables {a a' : A}
Definition eq_of_up_eq_up (p : up a = up a') : a = a'.
  lift.encode p

Definition lift_transport {P : A -> Type} (p : a = a') (z : lift (P a))
    : p # z = up (p # down z).
  by induction p; induction z; reflexivity
Defined.

  variables {A' : Type} (f : A -> A') (g : lift A -> lift A')
Definition lift_functor : lift A -> lift A'
  | lift_functor (up a) . up (f a)

Definition is_equiv_lift_functor [Hf : is_equiv f] : is_equiv (lift_functor f).
  adjointify (lift_functor f)
             (lift_functor f^-1)
             abstract begin
               intro z', induction z' with a',
               esimp, exact ap up !right_inv
             end end
             abstract begin
               intro z, induction z with a,
               esimp, exact ap up !left_inv
             end end

Definition lift_equiv_lift_of_is_equiv [Hf : is_equiv f] : lift A <~> lift A'.
  equiv.mk _ (is_equiv_lift_functor f)

Definition lift_equiv_lift (f : A <~> A') : lift A <~> lift A'.
  equiv.mk _ (is_equiv_lift_functor f)

Definition lift_equiv_lift_refl (A : Type) : lift_equiv_lift (erfl : A <~> A) = erfl.
  by apply equiv_eq; intro z; induction z with a; reflexivity

Definition lift_inv_functor [unfold_full] (a : A) : A'.
  down (g (up a))

Definition is_equiv_lift_inv_functor [Hf : is_equiv g]
    : is_equiv (lift_inv_functor g).
  adjointify (lift_inv_functor g)
             (lift_inv_functor g^-1)
             abstract begin
               intro z', rewrite [▸*,lift.eta,right_inv g],
             end end
             abstract begin
               intro z', rewrite [▸*,lift.eta,left_inv g],
             end end

Definition equiv_of_lift_equiv_lift (g : lift A <~> lift A') : A <~> A'.
  equiv.mk _ (is_equiv_lift_inv_functor g)

Definition lift_functor_left_inv  : lift_inv_functor (lift_functor f) = f.
  eq_of_homotopy (fun a => idp)

Definition lift_functor_right_inv : lift_functor (lift_inv_functor g) = g.
Proof.
    apply eq_of_homotopy, intro z, induction z with a, esimp, apply lift.eta
Defined.

  variables (A A')
Definition is_equiv_lift_functor_fn
    : is_equiv (lift_functor : (A -> A') -> (lift A -> lift A')).
  adjointify lift_functor
             lift_inv_functor
             lift_functor_right_inv
             lift_functor_left_inv

Definition lift_imp_lift_equiv : (lift A -> lift A') <~> (A -> A').
  (equiv.mk _ (is_equiv_lift_functor_fn A A'))^-1ᵉ

  (* can we deduce this from lift_imp_lift_equiv? *)
Definition lift_equiv_lift_equiv : (lift A <~> lift A') <~> (A <~> A').
  equiv.MK equiv_of_lift_equiv_lift
           lift_equiv_lift
           abstract begin
             intro f, apply equiv_eq, reflexivity
           end end
           abstract begin
             intro g, apply equiv_eq', esimp, apply eq_of_homotopy, intro z,
             induction z with a, esimp, apply lift.eta
           end end

Definition lift_eq_lift_equiv.{u1 u2} (A A' : Type.{u1})
    : (lift.{u1 u2} A = lift.{u1 u2} A') <~> (A = A').
  !eq_equiv_equiv @e !lift_equiv_lift_equiv @e !eq_equiv_equiv^-1ᵉ

Definition is_embedding_lift [instance] : is_embedding lift.
Proof.
    intro A A', fapply is_equiv.homotopy_closed,
      exact to_inv !lift_eq_lift_equiv,
      exact _,
    { intro p, induction p,
      esimp [lift_eq_lift_equiv,equiv.trans,equiv.symm,eq_equiv_equiv],
      rewrite [equiv_of_eq_refl, lift_equiv_lift_refl],
      apply ua_refl}
Defined.

Definition plift (A : pType.{u}) : pType.{max u v}.
  pointed.MK (lift A) (up (point _))

Definition plift_functor {A B : pType} (f : A ->* B) : plift A ->* plift B.
  Build_pMap (lift_functor f) (ap up (point_eq f))

  (* is_trunc_lift is defined in init.trunc *)

Definition pup {A : pType} : A ->* plift A.
  Build_pMap up idp

Definition pdown {A : pType} : plift A ->* A.
  Build_pMap down idp

Definition plift_functor_phomotopy {A B : pType} (f : A ->* B)
    : pdown o* plift_functor f o* pup ==* f.
Proof.
    fapply Build_pHomotopy,
    { reflexivity},
    { esimp, refine (concat_1p _) @ _, refine _ @ ap02 down (concat_1p _)^-1,
      refine _ @ !ap_compose, exact !ap_id^-1}
Defined.

Definition pequiv_plift (A : pType) : A <~>* plift A.
  pequiv_of_equiv (equiv_lift A) idp

Definition fiber_lift_functor {A B : Type} (f : A -> B) (b : B) :
    fiber (lift_functor f) (up b) <~> fiber f b.
Proof.
    fapply equiv.MK: intro v; cases v with a p,
    { cases a with a, exact fiber.mk a (eq_of_fn_eq_fn' up p) },
    { exact fiber.mk (up a) (ap up p) },
    { apply ap (fiber.mk a), apply eq_of_fn_eq_fn'_ap },
    { cases a with a, esimp, apply ap (fiber.mk (up a)), apply ap_eq_of_fn_eq_fn' }
Defined.


Defined. lift
