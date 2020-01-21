(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about 2-dimensional paths
*)

import .cubical.square .function
open function is_equiv equiv

namespace eq
  variables {A B C : Type} {f : A -> B} {a a' a₁ a₂ a₃ a₄ : A} {b b' : B}

Definition ap_is_constant_eq (p : forall x, f x = b) (q : a = a') :
  ap_is_constant p q =
  eq_con_inv_of_con_eq ((eq_of_square (square_of_pathover (apd p q)))^-1 @
  whisker_left (p a) (ap_constant q b)).
Proof.
  induction q, esimp, generalize (p a), intro p, cases p, apply idpath idp
Defined.

Definition ap_inv2 {p q : a = a'} (r : p = q)
  : square (ap (ap f) (inverse2 r))
  (inverse2 (ap (ap f) r))
  (ap_inv f p)
  (ap_inv f q).
  by induction r;exact hrfl

Definition ap_con2 {p₁ q₁ : a₁ = a₂} {p₂ q₂ : a₂ = a₃} (r₁ : p₁ = q₁) (r₂ : p₂ = q₂)
  : square (ap (ap f) (r₁ ◾ r₂))
  (ap (ap f) r₁ ◾ ap (ap f) r₂)
  (ap_con f p₁ p₂)
  (ap_con f q₁ q₂).
  by induction r₂;induction r₁;exact hrfl

Definition ap_con_right_inv_sq {A B : Type} {a1 a2 : A} (f : A -> B) (p : a1 = a2) :
  square (ap (ap f) (con.right_inv p))
  (con.right_inv (ap f p))
  (ap_con f p p^-1 @ whisker_left _ (ap_inv f p))
  idp.
  by cases p;apply hrefl

Definition ap_con_left_inv_sq {A B : Type} {a1 a2 : A} (f : A -> B) (p : a1 = a2) :
  square (ap (ap f) (con.left_inv p))
  (con.left_inv (ap f p))
  (ap_con f p^-1 p @ whisker_right _ (ap_inv f p))
  idp.
  by cases p;apply vrefl

Definition ap02_compose {A B C : Type} (g : B -> C) (f : A -> B) {a a' : A}
  {p₁ p₂ : a = a'} (q : p₁ = p₂) :
  square (ap_compose g f p₁) (ap_compose g f p₂) (ap02 (g o f) q) (ap02 g (ap02 f q)).
  by induction q; exact vrfl

Definition ap02_id {A : Type} {a a' : A}
  {p₁ p₂ : a = a'} (q : p₁ = p₂) :
  square (ap_id p₁) (ap_id p₂) (ap02 id q) q.
  by induction q; exact vrfl

Definition ap_ap_is_constant {A B C : Type} (g : B -> C) {f : A -> B} {b : B}
  (p : forall x, f x = b) {x y : A} (q : x = y) :
  square (ap (ap g) (ap_is_constant p q))
  (ap_is_constant (fun a => ap g (p a)) q)
  (ap_compose g f q)^-1
  ((ap_pp _ _ _) @ whisker_left _ !ap_inv).
Proof.
  induction q, esimp, generalize (p x), intro p, cases p, apply ids
(*    induction q, rewrite [↑ap_compose,ap_inv], apply hinverse, apply ap_con_right_inv_sq, *)
Defined.

Definition ap_ap_compose {A B C D : Type} (h : C -> D) (g : B -> C) (f : A -> B)
  {x y : A} (p : x = y) :
  square (ap_compose (h o g) f p)
  (ap (ap h) (ap_compose g f p))
  (ap_compose h (g o f) p)
  (ap_compose h g (ap f p)).
  by induction p;exact ids

Definition ap_compose_inv {A B C : Type} (g : B -> C) (f : A -> B)
  {x y : A} (p : x = y) :
  square (ap_compose g f p^-1)
  (inverse2 (ap_compose g f p) @ (ap_inv g (ap f p))^-1)
  (ap_inv (g o f) p)
  (ap (ap g) (ap_inv f p)).
  by induction p;exact ids

Definition ap_compose_con (g : B -> C) (f : A -> B) (p : a₁ = a₂) (q : a₂ = a₃) :
  square (ap_compose g f (p @ q))
  (ap_compose g f p ◾ ap_compose g f q @ (ap_con g (ap f p) (ap f q))^-1)
  (ap_con (g o f) p q)
  (ap (ap g) (ap_con f p q)).
  by induction q;induction p;exact ids

Definition ap_compose_natural {A B C : Type} (g : B -> C) (f : A -> B)
  {x y : A} {p q : x = y} (r : p = q) :
  square (ap (ap (g o f)) r)
  (ap (ap g o ap f) r)
  (ap_compose g f p)
  (ap_compose g f q).
  natural_square_tr (ap_compose g f) r

Definition whisker_right_eq_of_con_inv_eq_idp {p q : a₁ = a₂} (r : p @ q^-1 = idp) :
  whisker_right q^-1 (eq_of_con_inv_eq_idp r) @ con.right_inv q = r.
  by induction q; esimp at r; cases r; reflexivity

Definition ap_eq_of_con_inv_eq_idp (f : A -> B) {p q : a₁ = a₂} (r : p @ q^-1 = idp)
  : ap02 f (eq_of_con_inv_eq_idp r) =
  eq_of_con_inv_eq_idp (whisker_left _ !ap_inv^-1 @ (ap_pp _ _ _)^-1 @ ap02 f r)
 .
  by induction q;esimp at *;cases r;reflexivity

Definition eq_of_con_inv_eq_idp_con2 {p p' q q' : a₁ = a₂} (r : p = p') (s : q = q')
  (t : p' @ q'^-1 = idp)
  : eq_of_con_inv_eq_idp (r ◾ inverse2 s @ t) = r @ eq_of_con_inv_eq_idp t @ s^-1.
  by induction s;induction r;induction q;reflexivity

Definition naturality_apd_eq {A : Type} {B : A -> Type} {a a₂ : A} {f g : forall a, B a}
  (H : f == g) (p : a = a₂)
  : apd f p = concato_eq (eq_concato (H a) (apd g p)) (H a₂)^-1.
Proof.
  induction p, esimp,
  generalizes [H a, g a], intro ga Ha, induction Ha,
  reflexivity
Defined.

Definition con_tr_idp {P : A -> Type} {x y : A} (q : x = y) (u : P x) :
  con_tr idp q u = ap (fun p => p # u) (idp_con q).
  by induction q;reflexivity

Definition eq_transport_Fl_idp_left {A B : Type} {a : A} {b : B} (f : A -> B) (q : f a = b)
  : eq_transport_Fl idp q = (concat_1p _)^-1.
  by induction q; reflexivity

Definition whisker_left_idp_con_eq_assoc
  {A : Type} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃)
  : whisker_left p (idp_con q)^-1 = con.assoc p idp q.
  by induction q; reflexivity

Definition whisker_left_inverse2 {A : Type} {a : A} {p : a = a} (q : p = idp)
  : whisker_left p q⁻² @ q = con.right_inv p.
  by cases q; reflexivity

Definition cast_fn_cast_square {A : Type} {B C : A -> Type} (f : forall (a), B a -> C a) {a₁ a₂ : A}
  (p : a₁ = a₂) (q : a₂ = a₁) (r : p @ q = idp) (b : B a₁) :
  cast (ap C q) (f (cast (ap B p) b)) = f b.
  have q^-1 = p, from inv_eq_of_idp_eq_con r^-1,
Proof. induction this, induction q, reflexivity end

Definition ap011_ap_square_right {A B C : Type} (f : A -> B -> C) {a a' : A} (p : a = a')
  {b₁ b₂ b₃ : B} {q₁₂ : b₁ = b₂} {q₂₃ : b₂ = b₃} {q₁₃ : b₁ = b₃} (r : q₁₂ @ q₂₃ = q₁₃) :
  square (ap011 f p q₁₂) (ap (fun x => f x b₃) p) (ap (f a) q₁₃) (ap (f a') q₂₃).
  by induction r; induction q₂₃; induction q₁₂; induction p; exact ids

Definition ap011_ap_square_left {A B C : Type} (f : B -> A -> C) {a a' : A} (p : a = a')
  {b₁ b₂ b₃ : B} {q₁₂ : b₁ = b₂} {q₂₃ : b₂ = b₃} {q₁₃ : b₁ = b₃} (r : q₁₂ @ q₂₃ = q₁₃) :
  square (ap011 f q₁₂ p) (ap (f b₃) p) (ap (fun x => f x a) q₁₃) (ap (fun x => f x a') q₂₃).
  by induction r; induction q₂₃; induction q₁₂; induction p; exact ids

Definition con2_assoc {A : Type} {x y z t : A} {p p' : x = y} {q q' : y = z} {r r' : z = t}
  (h : p = p') (h' : q = q') (h'' : r = r') :
  square ((h ◾ h') ◾ h'') (h ◾ (h' ◾ h'')) (con.assoc p q r) (con.assoc p' q' r').
  by induction h; induction h'; induction h''; exact hrfl

Definition con_left_inv_idp {A : Type} {x : A} {p : x = x} (q : p = idp)
  : con.left_inv p = q⁻² ◾ q.
  by cases q; reflexivity

Definition eckmann_hilton_con2 {A : Type} {x : A} {p p' q q': idp = idp :> x = x}
  (h : p = p') (h' : q = q') : square (h ◾ h') (h' ◾ h) (eckmann_hilton p q) (eckmann_hilton p' q').
  by induction h; induction h'; exact hrfl

Definition ap_con_fn {A B : Type} {a a' : A} {b : B} (g h : A -> b = b) (p : a = a') :
  ap (fun a => g a @ h a) p = ap g p ◾ ap h p.
  by induction p; reflexivity

Definition ap_eq_ap011 {A B C X : Type} (f : A -> B -> C) (g : X -> A) (h : X -> B) {x x' : X}
  (p : x = x') : ap (fun x => f (g x) (h x)) p = ap011 f (ap g p) (ap h p).
  by induction p; reflexivity

Definition ap_is_weakly_constant {A B : Type} {f : A -> B}
  (h : is_weakly_constant f) {a a' : A} (p : a = a') : ap f p = (h a a)^-1 @ h a a'.
  by induction p; exact (con_Vp _)^-1

Definition ap_is_constant_idp {A B : Type} {f : A -> B} {b : B} (p : forall a, f a = b) {a : A} (q : a = a)
  (r : q = idp) : ap_is_constant p q = ap02 f r @ (con.right_inv (p a))^-1.
  by cases r; exact (concat_1p _)^-1

Definition con_right_inv_natural {A : Type} {a a' : A} {p p' : a = a'} (q : p = p') :
  con.right_inv p = q ◾ q⁻² @ con.right_inv p'.
  by induction q; induction p; reflexivity

Definition whisker_right_ap {A B : Type} {a a' : A}{b₁ b₂ b₃ : B} (q : b₂ = b₃) (f : A -> b₁ = b₂)
  (p : a = a') : whisker_right q (ap f p) = ap (fun a => f a @ q) p.
  by induction p; reflexivity

Definition ap02_ap_constant {A B C : Type} {a a' : A} (f : B -> C) (b : B) (p : a = a') :
  square (ap_constant p (f b)) (ap02 f (ap_constant p b)) (ap_compose f (fun x => b) p) idp.
  by induction p; exact ids

Definition ap_constant_compose {A B C : Type} {a a' : A} (c : C) (f : A -> B) (p : a = a') :
  square (ap_constant p c) (ap_constant (ap f p) c) (ap_compose (fun x => c) f p) idp.
  by induction p; exact ids

Definition ap02_constant {A B : Type} {a a' : A} (b : B) {p p' : a = a'}
  (q : p = p') : square (ap_constant p b) (ap_constant p' b) (ap02 (fun x => b) q) idp.
  by induction q; exact vrfl

  section hsquare
  variables {A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : Type}
  {f₁₀ : A₀₀ -> A₂₀} {f₃₀ : A₂₀ -> A₄₀}
  {f₀₁ : A₀₀ -> A₀₂} {f₂₁ : A₂₀ -> A₂₂} {f₄₁ : A₄₀ -> A₄₂}
  {f₁₂ : A₀₂ -> A₂₂} {f₃₂ : A₂₂ -> A₄₂}
  {f₀₃ : A₀₂ -> A₀₄} {f₂₃ : A₂₂ -> A₂₄} {f₄₃ : A₄₂ -> A₄₄}
  {f₁₄ : A₀₄ -> A₂₄} {f₃₄ : A₂₄ -> A₄₄}

Definition hsquare (f₁₀ : A₀₀ -> A₂₀) (f₁₂ : A₀₂ -> A₂₂)
  (f₀₁ : A₀₀ -> A₀₂) (f₂₁ : A₂₀ -> A₂₂) : Type.
  f₂₁ o f₁₀ == f₁₂ o f₀₁

Definition hsquare_of_homotopy (p : f₂₁ o f₁₀ == f₁₂ o f₀₁) : hsquare f₁₀ f₁₂ f₀₁ f₂₁.
  p

Definition homotopy_of_hsquare (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) : f₂₁ o f₁₀ == f₁₂ o f₀₁.
  p

Definition homotopy_top_of_hsquare {f₂₁ : A₂₀ <~> A₂₂} (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) :
  f₁₀ == f₂₁^-1 o f₁₂ o f₀₁.
  homotopy_inv_of_homotopy_post _ _ _ p

Definition homotopy_top_of_hsquare' [is_equiv f₂₁] (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) :
  f₁₀ == f₂₁^-1 o f₁₂ o f₀₁.
  homotopy_inv_of_homotopy_post _ _ _ p

Definition hhconcat (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) (q : hsquare f₃₀ f₃₂ f₂₁ f₄₁) :
  hsquare (f₃₀ o f₁₀) (f₃₂ o f₁₂) f₀₁ f₄₁.
  hwhisker_right f₁₀ q @hty hwhisker_left f₃₂ p

Definition hvconcat (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) (q : hsquare f₁₂ f₁₄ f₀₃ f₂₃) :
  hsquare f₁₀ f₁₄ (f₀₃ o f₀₁) (f₂₃ o f₂₁).
  (hhconcat p^-1ʰᵗʸ q^-1ʰᵗʸ)^-1ʰᵗʸ

Definition hhinverse {f₁₀ : A₀₀ <~> A₂₀} {f₁₂ : A₀₂ <~> A₂₂} (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) :
  hsquare f₁₀^-1ᵉ f₁₂^-1ᵉ f₂₁ f₀₁.
  fun b => eq_inv_of_eq ((p (f₁₀^-1ᵉ b))^-1 @ ap f₂₁ (to_right_inv f₁₀ b))

Definition hvinverse {f₀₁ : A₀₀ <~> A₀₂} {f₂₁ : A₂₀ <~> A₂₂} (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) :
  hsquare f₁₂ f₁₀ f₀₁^-1ᵉ f₂₁^-1ᵉ.
  (hhinverse p^-1ʰᵗʸ)^-1ʰᵗʸ

  infix ` @htyh `:73 . hhconcat
  infix ` @htyv `:73 . hvconcat
  postfix `^-1ʰᵗʸʰ`:(max+1) . hhinverse
  postfix `^-1ʰᵗʸᵛ`:(max+1) . hvinverse

Defined. hsquare

Defined. eq
