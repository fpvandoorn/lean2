(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Definition of general colimits and sequential colimits.
*)

(*Definition of a general colimit *)
open eq nat quotient sigma equiv is_trunc

namespace colimit
section
  parameters {I J : Type} (A : I -> Type) (dom cod : J -> I)
  (f : forall (j : J), A (dom j) -> A (cod j))
  variables {i : I} (a : A i) (j : J) (b : A (dom j))

  local abbreviation B . Σ(i : I), A i
  inductive colim_rel : B -> B -> Type.
  | Rmk : forall {j : J} (a : A (dom j)), colim_rel ⟨cod j, f j a⟩ ⟨dom j, a⟩
  open colim_rel
  local abbreviation R . colim_rel

  (* TODO: define this in root namespace *)
Definition colimit : Type.
  quotient colim_rel

Definition incl : colimit.
  class_of R ⟨i, a⟩
  abbreviation ι . @incl

Definition cglue : ι (f j b) = ι b.
  eq_of_rel colim_rel (Rmk f b)

  protectedDefinition rec {P : colimit -> Type}
  (Pincl : forall (i : I) (x : A i), P (ι x))
  (Pglue : forall (j : J) (x : A (dom j)), Pincl (f j x) =[cglue j x] Pincl x)
  (y : colimit) : P y.
Proof.
  fapply (quotient.rec_on y),
  { intro a, cases a, apply Pincl},
  { intro a a' H, cases H, apply Pglue}
Defined.

  protectedDefinition rec_on {P : colimit -> Type} (y : colimit)
  (Pincl : forall (i : I) (x : A i), P (ι x))
  (Pglue : forall (j : J) (x : A (dom j)), Pincl (f j x) =[cglue j x] Pincl x) : P y.
  rec Pincl Pglue y

Definition rec_cglue {P : colimit -> Type}
  (Pincl : forall (i : I) (x : A i), P (ι x))
  (Pglue : forall (j : J) (x : A (dom j)), Pincl (f j x) =[cglue j x] Pincl x)
  {j : J} (x : A (dom j)) : apd (rec Pincl Pglue) (cglue j x) = Pglue j x.
  !rec_eq_of_rel

  protectedDefinition elim {P : Type} (Pincl : forall (i : I) (x : A i), P)
  (Pglue : forall (j : J) (x : A (dom j)), Pincl (f j x) = Pincl x) (y : colimit) : P.
  rec Pincl (fun j a => pathover_of_eq _ (Pglue j a)) y

  protectedDefinition elim_on {P : Type} (y : colimit)
  (Pincl : forall (i : I) (x : A i), P)
  (Pglue : forall (j : J) (x : A (dom j)), Pincl (f j x) = Pincl x) : P.
  elim Pincl Pglue y

Definition elim_cglue {P : Type}
  (Pincl : forall (i : I) (x : A i), P)
  (Pglue : forall (j : J) (x : A (dom j)), Pincl (f j x) = Pincl x)
  {j : J} (x : A (dom j)) : ap (elim Pincl Pglue) (cglue j x) = Pglue j x.
Proof.
  apply eq_of_fn_eq_fn_inv !(pathover_constant (cglue j x)),
  rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim,rec_cglue],
Defined.

  protectedDefinition elim_type (Pincl : forall (i : I) (x : A i), Type)
  (Pglue : forall (j : J) (x : A (dom j)), Pincl (f j x) <~> Pincl x) (y : colimit) : Type.
  elim Pincl (fun j a => ua (Pglue j a)) y

  protectedDefinition elim_type_on (y : colimit)
  (Pincl : forall (i : I) (x : A i), Type)
  (Pglue : forall (j : J) (x : A (dom j)), Pincl (f j x) <~> Pincl x) : Type.
  elim_type Pincl Pglue y

Definition elim_type_cglue (Pincl : forall (i : I) (x : A i), Type)
  (Pglue : forall (j : J) (x : A (dom j)), Pincl (f j x) <~> Pincl x)
  {j : J} (x : A (dom j)) : transport (elim_type Pincl Pglue) (cglue j x) = Pglue j x.
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_cglue];apply cast_ua_fn

  protectedDefinition rec_prop {P : colimit -> Type} [H : forall x, is_prop (P x)]
  (Pincl : forall (i : I) (x : A i), P (ι x)) (y : colimit) : P y.
  rec Pincl (fun a b => !is_prop.elimo) y

  protectedDefinition elim_prop {P : Type} [H : is_prop P] (Pincl : forall (i : I) (x : A i), P)
  (y : colimit) : P.
  elim Pincl (fun a b => !is_prop.elim) y

Defined.
Defined. colimit

(*Definition of a sequential colimit *)
namespace seq_colim
section
  (*
  we define it directly in terms of quotients. An alternativeDefinition could be
Definition seq_colim . colimit.colimit A id succ f
  *)
  parameters {A : ℕ -> Type} (f : forall (n), A n -> A (succ n))
  variables {n : ℕ} (a : A n)

  local abbreviation B . Σ(n : ℕ), A n
  inductive seq_rel : B -> B -> Type.
  | Rmk : forall {n : ℕ} (a : A n), seq_rel ⟨succ n, f a⟩ ⟨n, a⟩
  open seq_rel
  local abbreviation R . seq_rel

  (* TODO: define this in root namespace *)
Definition seq_colim : Type.
  quotient seq_rel

Definition inclusion : seq_colim.
  class_of R ⟨n, a⟩

  abbreviation sι . @inclusion

Definition glue : sι (f a) = sι a.
  eq_of_rel seq_rel (Rmk f a)

  protectedDefinition rec {P : seq_colim -> Type}
  (Pincl : forall (n : ℕ) (a : A n), P (sι a))
  (Pglue : forall (n : ℕ) (a : A n), Pincl (f a) =[glue a] Pincl a) (aa : seq_colim) : P aa.
Proof.
  fapply (quotient.rec_on aa),
  { intro a, cases a, apply Pincl},
  { intro a a' H, cases H, apply Pglue}
Defined.

  protectedDefinition rec_on {P : seq_colim -> Type} (aa : seq_colim)
  (Pincl : forall (n : ℕ) (a : A n), P (sι a))
  (Pglue : forall (n : ℕ) (a : A n), Pincl (f a) =[glue a] Pincl a)
  : P aa.
  rec Pincl Pglue aa

Definition rec_glue {P : seq_colim -> Type} (Pincl : forall (n : ℕ) (a : A n), P (sι a))
  (Pglue : forall (n : ℕ) (a : A n), Pincl (f a) =[glue a] Pincl a) {n : ℕ} (a : A n)
  : apd (rec Pincl Pglue) (glue a) = Pglue a.
  !rec_eq_of_rel

  protectedDefinition elim {P : Type} (Pincl : forall (n : ℕ) (a : A n), P)
  (Pglue : forall (n : ℕ) (a : A n), Pincl (f a) = Pincl a) : seq_colim -> P.
  rec Pincl (fun n a => pathover_of_eq _ (Pglue a))

  protectedDefinition elim_on {P : Type} (aa : seq_colim)
  (Pincl : forall (n : ℕ) (a : A n), P)
  (Pglue : forall (n : ℕ) (a : A n), Pincl (f a) = Pincl a) : P.
  elim Pincl Pglue aa

Definition elim_glue {P : Type} (Pincl : forall (n : ℕ) (a : A n), P)
  (Pglue : forall (n : ℕ) (a : A n), Pincl (f a) = Pincl a) {n : ℕ} (a : A n)
  : ap (elim Pincl Pglue) (glue a) = Pglue a.
Proof.
  apply eq_of_fn_eq_fn_inv !(pathover_constant (glue a)),
  rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim,rec_glue],
Defined.

  protectedDefinition elim_type (Pincl : forall (n : ℕ) (a : A n), Type)
  (Pglue : forall (n : ℕ) (a : A n), Pincl (f a) <~> Pincl a) : seq_colim -> Type.
  elim Pincl (fun n a => ua (Pglue a))

  protectedDefinition elim_type_on (aa : seq_colim)
  (Pincl : forall (n : ℕ) (a : A n), Type)
  (Pglue : forall (n : ℕ) (a : A n), Pincl (f a) <~> Pincl a) : Type.
  elim_type Pincl Pglue aa

Definition elim_type_glue (Pincl : forall (n : ℕ) (a : A n), Type)
  (Pglue : forall (n : ℕ) (a : A n), Pincl (f a) <~> Pincl a) {n : ℕ} (a : A n)
  : transport (elim_type Pincl Pglue) (glue a) = Pglue a.
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_glue]; apply cast_ua_fn

Definition elim_type_glue_inv (Pincl : forall (n : ℕ) (a : A n), Type)
  (Pglue : forall (n : ℕ) (a : A n), Pincl (f a) <~> Pincl a) {n : ℕ} (a : A n)
  : transport (seq_colim.elim_type f Pincl Pglue) (glue a)^-1 = to_inv (Pglue a).
  by rewrite [tr_eq_cast_ap_fn, ↑seq_colim.elim_type, ap_inv, elim_glue]; apply cast_ua_inv_fn

  protectedDefinition rec_prop {P : seq_colim -> Type} [H : forall x, is_prop (P x)]
  (Pincl : forall (n : ℕ) (a : A n), P (sι a)) (aa : seq_colim) : P aa.
  rec Pincl (fun a b => !is_prop.elimo) aa

  protectedDefinition elim_prop {P : Type} [H : is_prop P] (Pincl : forall (n : ℕ) (a : A n), P)
  : seq_colim -> P.
  elim Pincl (fun a b => !is_prop.elim)


Defined.
Defined. seq_colim










