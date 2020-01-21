(*
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

Pointed and unpointed type functor => and adjoint pairs.
More or less ported from Evan Cavallo's HoTT-Agda homotopy library.
*)

import types.pointed

open equiv function pointed

structure type_functor : Type.
  (fun_ty : Type -> Type)
  (fun_arr : forall , (A -> B) -> (fun_ty A -> fun_ty B))
  (respect_id : forall {A}, fun_arr (@id A) = id)
  (respect_comp : forall {A B C} (g : B -> C) (f : A -> B),
    fun_arr (g o f) = (fun_arr g) o (fun_arr f))



section type_adjoint
open type_functor

structure type_adjoint (F G : type_functor) : Type.
  (η : forall X, X -> G (F X))
  (ε : forall U, F (G U) -> U)
  (ηnat : forall X Y (h : X -> Y), η Y o h = fun_arr G (fun_arr F h) o η X)
  (εnat : forall U V (k : U -> V), ε V o fun_arr F (fun_arr G k) = k o ε U)
  (εF_Fη : forall X, ε (F X) o fun_arr F (η X) = id)
  (Gε_ηG : forall U, fun_arr G (ε U) o η (G U) = id)

Defined. type_adjoint

structure Type_functor : Type.
  (fun_ty : pType -> pType)
  (fun_arr : forall , (A ->* B) -> (fun_ty A ->* fun_ty B))
  (respect_id : forall {A}, fun_arr (pid A) = pid (fun_ty A))
  (respect_comp : forall {A B C} (g : B ->* C) (f : A ->* B),
    fun_arr (g o* f) = fun_arr g o* fun_arr f)



section Type_adjoint
open Type_functor

structure Type_adjoint (F G : Type_functor) : Type.
  (η : forall (X : pType), X ->* G (F X))
  (ε : forall (U : pType), F (G U) ->* U)
  (ηnat : forall {X Y} (h : X ->* Y), η Y o* h = (fun_arr G (fun_arr F h)) o* η X)
  (εnat : forall {U V} (k : U ->* V), ε V o* (fun_arr F (fun_arr G k)) = k o* ε U)
  (εF_Fη : forall {X}, ε (F X) o* (fun_arr F (η X)) = !pid)
  (Gε_ηG : forall {U}, (fun_arr G (ε U)) o* η (G U) = !pid)

Defined. Type_adjoint
