(*
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

TheDefinition of pointed types. This file is here to avoid circularities in the import graph
*)

prelude
import init.trunc

open eq equiv is_equiv is_trunc

structure pointed [class] (A : Type).
  (point : A)

structure pType.
  (carrier : Type)
  (Point   : carrier)

notation `pType` . pType

namespace pointed
  attribute pType.carrier [coercion]
  variables {A : Type}

Definition (point _) [H : pointed A] . point A
Definition Point (A : pType) . pType.Point A
Definition carrier (A : pType) . pType.carrier A
  protectedDefinition Mk {A : Type} (a : A) . Build_pType A a
  protectedDefinition MK (A : Type) (a : A) . Build_pType A a
  protectedDefinition mk' (A : Type) [H : pointed A] : pType.
  Build_pType A (point A)
Definition pointed_carrier [instance] (A : pType) : pointed A.
  pointed.mk (Point A)

Defined. pointed
open pointed

section
  universe variable u
  structure ptrunctype (n : ℕ₋₂) extends trunctype.{u} n, pType.{u}

Definition is_trunc_ptrunctype [instance] {n : ℕ₋₂} (X : ptrunctype n)
    : is_trunc n (ptrunctype.to_pType X).
  trunctype.struct X

Defined.

notation n `-pType` . ptrunctype n
abbreviation pSet  [parsing_only] . 0-pType
notation `Set*` . pSet

namespace pointed

  protectedDefinition ptrunctype.mk' (n : ℕ₋₂)
    (A : Type) [pointed A] [is_trunc n A] : n-pType.
  ptrunctype.mk A _ pt

  protectedDefinition pSet.mk . @ptrunctype.mk (-1.+1)
  protectedDefinition pSet.mk' . ptrunctype.mk' (-1.+1)

Definition ptrunctype_of_trunctype {n : ℕ₋₂} (A : n-Type) (a : A)
    : n-pType.
  ptrunctype.mk A _ a

Definition ptrunctype_of_pType {n : ℕ₋₂} (A : pType) (H : is_trunc n A)
    : n-pType.
  ptrunctype.mk A _ pt

Definition pSet_of_Set (A : Set) (a : A) : Set*.
  ptrunctype.mk A _ a

Definition pSet_of_pType (A : pType) (H : is_set A) : Set*.
  ptrunctype.mk A _ pt

  attribute ptrunctype._trans_of_to_pType ptrunctype.to_pType ptrunctype.to_trunctype [unfold 2]

  (* Any contractible type is pointed *)
Definition pointed_of_is_contr [instance] [priority 800]
    (A : Type) [H : is_contr A] : pointed A.
  pointed.mk !center

Defined. pointed

(* pointed maps *)
structure ppi {A : pType} (P : A -> Type) (x₀ : P (point _)).
  (to_fun : forall , P a)
  (resp_pt : to_fun (Point A) = x₀)

Definition pppi' {A : pType} (P : A -> pType) : Type.
ppi P pt

Definition ppi_const {A : pType} (P : A -> pType) : pppi' P.
ppi.mk (fun a => (point _)) idp

Definition pppi {A : pType} (P : A -> pType) : pType.
pointed.MK (pppi' P) (ppi_const P)

(* do we want to make this already pointed? *)
Definition pmap (A B : pType) : Type . @pppi A (fun a => B)



infix ` ->* `:28 . pmap
notation `ppforall ` binders `, ` r:(scoped P, pppi P) . r


namespace pointed


Definition pppi.mk {A : pType} {P : A -> pType} (f : forall a, P a)
    (p : f (point _) = (point _)) : pppi P.
  ppi.mk f p

Definition pppi.to_fun [coercion] {A : pType} {P : A -> pType} (f : pppi' P)
    (a : A) : P a.
  ppi.to_fun f a

	Definition Build_pMap {A B : pType} (f : A -> B)
    (p : f (Point A) = Point B) : A ->* B.
	pppi.mk f p

  abbreviation pmap.to_fun [coercion] {A B : pType} (f : A ->* B) : A -> B.
  pppi.to_fun f

Definition point_eq {A : pType} {P : A -> Type} {p₀ : P (point _)}
    (f : ppi P p₀) : f (point _) = p₀.
  ppi.resp_pt f

  (* notation `ppforall ` binders `, ` r:(scoped P, ppi _ P) . r *)
  (*Definition pmxap.mk {A B : pType} (f : A -> B) (p : f (point _) = (point _)) : A ->* B . *)
  (* ppi.mk f p *)
  (*Definition pmap.to_fun [coercion] {A B : pType} (f : A ->* B) : A -> B . f *)

Defined. pointed open pointed

(* pointed homotopies *)
Definition phomotopy {A : pType} {P : A -> Type} {p₀ : P (point _)} (f g : ppi P p₀) : Type.
ppi (fun a => f a = g a) (point_eq f @ (point_eq g)^-1)

(* structure phomotopy {A B : pType} (f g : A ->* B) : Type . *)
(*   (homotopy : f == g) *)
(*   (homotopy_pt : homotopy (point _) @ point_eq g = point_eq f) *)

namespace pointed
  variables {A : pType} {P : A -> Type} {p₀ : P (point _)} {f g : ppi P p₀}

  infix ` ==* `:50 . phomotopy
Definition Build_pHomotopy (h : f == g)
    (p : h (point _) @ point_eq g = point_eq f) : f ==* g.
  ppi.mk h (eq_con_inv_of_con_eq p)

Definition to_homotopy [coercion] (p : f ==* g) : forall a, f a = g a . p
Definition point_htpy (p : f ==* g) :
    p (point _) @ point_eq g = point_eq f.
  con_eq_of_eq_con_inv (point_eq p)


Defined. pointed
