(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Coherence conditions for operations on pathovers
*)

open function equiv

namespace eq

  variables {A A' A'' : Type} {B B' : A -> Type} {B'' : A' -> Type} {C : forall (a), B a -> Type}
  {a a₂ a₃ a₄ : A} {p p' p'' : a = a₂} {p₂ p₂' : a₂ = a₃} {p₃ : a₃ = a₄} {p₁₃ : a = a₃}
  {a' : A'}
  {b b' : B a} {b₂ b₂' : B a₂} {b₃ : B a₃} {b₄ : B a₄}
  {c : C b} {c₂ : C b₂}

Definition pathover_ap_id (q : b =[p] b₂) : pathover_ap B id q = change_path (ap_id p)^-1 q.
  by induction q; reflexivity

Definition pathover_ap_compose (B : A'' -> Type) (g : A' -> A'') (f : A -> A')
  {b : B (g (f a))} {b₂ : B (g (f a₂))} (q : b =[p] b₂) : pathover_ap B (g o f) q
  = change_path (ap_compose g f p)^-1 (pathover_ap B g (pathover_ap (B o g) f q)).
  by induction q; reflexivity

Definition pathover_ap_compose_rev (B : A'' -> Type) (g : A' -> A'') (f : A -> A')
  {b : B (g (f a))} {b₂ : B (g (f a₂))} (q : b =[p] b₂) :
  pathover_ap B g (pathover_ap (B o g) f q)
  = change_path (ap_compose g f p) (pathover_ap B (g o f) q).
  by induction q; reflexivity

Definition pathover_of_tr_eq_idp (r : b = b') : pathover_of_tr_eq r = pathover_idp_of_eq r.
  idp

Definition pathover_of_tr_eq_eq_concato (r : p # b = b₂)
  : pathover_of_tr_eq r = pathover_tr p b @o pathover_idp_of_eq r.
  by induction r; induction p; reflexivity

Definition apd011_eq_apo11_apd (f : forall a, B a -> A') (p : a = a₂) (q : b =[p] b₂)
  : apd011 f p q = apo11_constant_right (apd f p) q.
  by induction q; reflexivity

Definition change_path_con (q : p = p') (q' : p' = p'') (r : b =[p] b₂) :
  change_path (q @ q') r = change_path q' (change_path q r).
  by induction q; induction q'; reflexivity

Definition change_path_invo (q : p = p') (r : b =[p] b₂) :
  change_path (inverse2 q) r^-1ᵒ = (change_path q r)^-1ᵒ.
  by induction q; reflexivity

Definition change_path_cono (q : p = p') (q₂ : p₂ = p₂') (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃):
  change_path (q ◾ q₂) (r @o r₂) = change_path q r @o change_path q₂ r₂.
  by induction q; induction q₂; reflexivity

Definition pathover_of_pathover_ap_invo (B' : A' -> Type) (f : A -> A')
  {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[ap f p] b₂) :
  pathover_of_pathover_ap B' f (change_path (ap_inv f p)^-1 q^-1ᵒ) =
  (pathover_of_pathover_ap B' f q)^-1ᵒ.
  by induction p; eapply idp_rec_on q; reflexivity

Definition pathover_of_pathover_ap_cono (B' : A' -> Type) (f : A -> A')
  {b : B' (f a)} {b₂ : B' (f a₂)} {b₃ : B' (f a₃)} (q : b =[ap f p] b₂) (q₂ : b₂ =[ap f p₂] b₃) :
  pathover_of_pathover_ap B' f (change_path (ap_con f p p₂)^-1 (q @o q₂)) =
  pathover_of_pathover_ap B' f q @o pathover_of_pathover_ap B' f q₂.
  by induction p; induction p₂; eapply idp_rec_on q; eapply idp_rec_on q₂; reflexivity

Definition pathover_ap_pathover_of_pathover_ap (P : A'' -> Type) (g : A' -> A'') (f : A -> A')
  {p : a = a₂} {b : P (g (f a))} {b₂ : P (g (f a₂))} (q : b =[ap f p] b₂) :
  pathover_ap P (g o f) (pathover_of_pathover_ap (P o g) f q) =
  change_path (ap_compose g f p)^-1 (pathover_ap P g q).
  by induction p; eapply (idp_rec_on q); reflexivity

Definition change_path_pathover_of_pathover_ap (B' : A' -> Type) (f : A -> A') {p p' : a = a₂}
  (r : p = p') {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[ap f p] b₂) :
  change_path r (pathover_of_pathover_ap B' f q) =
  pathover_of_pathover_ap B' f (change_path (ap02 f r) q).
  by induction r; reflexivity

Definition pathover_ap_change_path (B' : A' -> Type) (f : A -> A') {p p' : a = a₂}
  (r : p = p') {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) :
  pathover_ap B' f (change_path r q) = change_path (ap02 f r) (pathover_ap B' f q).
  by induction r; reflexivity

Definition change_path_equiv (b : B a) (b₂ : B a₂) (q : p = p')
  : (b =[p] b₂) <~> (b =[p'] b₂).
Proof.
  fapply equiv.MK,
  { exact change_path q},
  { exact change_path q^-1},
  { intro r, induction q, reflexivity},
  { intro r, induction q, reflexivity},
Defined.

Definition apd_ap {B : A' -> Type} (g : forall b, B b) (f : A -> A') (p : a = a₂)
  :  apd g (ap f p) = pathover_ap B f (apd (fun x => g (f x)) p) .
  by induction p; reflexivity

Definition apd_eq_apd_ap {B : A' -> Type} (g : forall b, B b) (f : A -> A') (p : a = a₂)
  : apd (fun x => g (f x)) p = pathover_of_pathover_ap B f (apd g (ap f p)).
  by induction p; reflexivity

Definition ap_compose_ap02_constant {A B C : Type} {a a' : A} (p : a = a') (b : B) (c : C) :
  ap_compose (fun c => b) (fun a => c) p @ ap02 (fun c => b) (ap_constant p c) = ap_constant p b.
  by induction p; reflexivity

Definition apd_constant (b : B'' a') (p : a = a) :
  pathover_ap B'' (fun a => a') (apd (fun a => b) p) = change_path (ap_constant p a')^-1 idpo.
Proof.
  rewrite [apd_eq_apd_ap _ _ p],
  let y . !change_path_of_pathover (apd (apd id) (ap_constant p b))^-1ᵒ,
  rewrite -y, esimp,
  refine !pathover_ap_pathover_of_pathover_ap @ _,
  rewrite pathover_ap_change_path,
  rewrite -change_path_con, apply ap (fun x => change_path x idpo),
  unfold ap02, rewrite [ap_inv,-con_inv], apply inverse2,
  apply ap_compose_ap02_constant
Defined.

Definition apd_constant' {A A' : Type} {B : A' -> Type} {a₁ a₂ : A} {a' : A'} (b : B a')
  (p : a₁ = a₂) : apd (fun x => b) p = pathover_of_eq p idp.
  by induction p; reflexivity

Definition apd_change_path {B : A -> Type} {a a₂ : A} (f : forall a, B a) {p p' : a = a₂} (s : p = p')
  : apd f p' = change_path s (apd f p).
  by induction s; reflexivity

Definition cono_invo_eq_idpo {q q' : b =[p] b₂} (r : q = q')
  : change_path (con.right_inv p) (q @o q'^-1ᵒ) = idpo.
  by induction r; induction q; reflexivity

Definition tr_eq_of_pathover_concato_eq {A : Type} {B : A -> Type} {a a' : A} {p : a = a'}
  {b : B a} {b' b'' : B a'} (q : b =[p] b') (r : b' = b'') :
  tr_eq_of_pathover (q @op r) = tr_eq_of_pathover q @ r.
  by induction r; reflexivity

Defined. eq
