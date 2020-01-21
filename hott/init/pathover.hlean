(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

BasicDefinitions about pathovers
*)

prelude
import .path .equiv

open equiv is_equiv function

variables {A A' : Type} {B B' : A -> Type} {B'' : A' -> Type} {C : forall (a), B a -> Type}
          {a a₂ a₃ a₄ : A} {p p' : a = a₂} {p₂ : a₂ = a₃} {p₃ : a₃ = a₄} {p₁₃ : a = a₃}
          {b b' : B a} {b₂ b₂' : B a₂} {b₃ : B a₃} {b₄ : B a₄}
          {c : C b} {c₂ : C b₂}

namespace eq
  inductive pathover.{l} (B : A -> Type.{l}) (b : B a) : forall {a₂ : A}, a = a₂ -> B a₂ -> Type.{l}.
  idpatho : pathover B b (refl a) b

  notation b ` =[`:50 p:0 `] `:0 b₂:50 . pathover _ b p b₂

Definition idpo : b =[refl a] b.
  pathover.idpatho b

Definition idpatho (b : B a) : b =[refl a] b.
  pathover.idpatho b

  (* equivalences with equality using transport *)
Definition pathover_of_tr_eq [unfold 5 8] (r : p # b = b₂) : b =[p] b₂.
  by cases p; cases r; constructor

Definition pathover_of_eq_tr [unfold 5 8] (r : b = p^-1 # b₂) : b =[p] b₂.
  by cases p; cases r; constructor

Definition tr_eq_of_pathover (r : b =[p] b₂) : p # b = b₂.
  by cases r; reflexivity

Definition eq_tr_of_pathover (r : b =[p] b₂) : b = p^-1 # b₂.
  by cases r; reflexivity

Definition pathover_equiv_tr_eq (p : a = a₂) (b : B a) (b₂ : B a₂)
    : (b =[p] b₂) <~> (p # b = b₂).
Proof.
    fapply equiv.MK,
    { exact tr_eq_of_pathover},
    { exact pathover_of_tr_eq},
    { intro r, cases p, cases r, apply idp},
    { intro r, cases r, apply idp},
Defined.

Definition pathover_equiv_eq_tr (p : a = a₂) (b : B a) (b₂ : B a₂)
    : (b =[p] b₂) <~> (b = p^-1 # b₂).
Proof.
    fapply equiv.MK,
    { exact eq_tr_of_pathover},
    { exact pathover_of_eq_tr},
    { intro r, cases p, cases r, apply idp},
    { intro r, cases r, apply idp},
Defined.

Definition pathover_tr (p : a = a₂) (b : B a) : b =[p] p # b.
  by cases p; constructor

Definition tr_pathover (p : a = a₂) (b : B a₂) : p^-1 # b =[p] b.
  by cases p; constructor

Definition concato [unfold 12] (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) : b =[p @ p₂] b₃.
  by induction r₂; exact r

Definition inverseo (r : b =[p] b₂) : b₂ =[p^-1] b.
  by induction r; constructor

Definition concato_eq [unfold 10] (r : b =[p] b₂) (q : b₂ = b₂') : b =[p] b₂'.
  by induction q; exact r

Definition eq_concato (q : b = b') (r : b' =[p] b₂) : b =[p] b₂.
  by induction q; exact r

Definition change_path (q : p = p') (r : b =[p] b₂) : b =[p'] b₂.
  q # r

Definition change_path_idp [unfold_full] (r : b =[p] b₂) : change_path idp r = r.
  by reflexivity

  (* infix ` @ ` . concato *)
  infix ` @o `:72 . concato
  infix ` @op `:73 . concato_eq
  infix ` @po `:74 . eq_concato
  (* postfix `^-1` . inverseo *)
  postfix `^-1ᵒ`:(max+10) . inverseo

Definition pathover_cancel_right (q : b =[p @ p₂] b₃) (r : b₃ =[p₂^-1] b₂) : b =[p] b₂.
  change_path !con_inv_cancel_right (q @o r)

Definition pathover_cancel_right' (q : b =[p₁₃ @ p₂^-1] b₂) (r : b₂ =[p₂] b₃) : b =[p₁₃] b₃.
  change_path !inv_con_cancel_right (q @o r)

Definition pathover_cancel_left (q : b₂ =[p^-1] b) (r : b =[p @ p₂] b₃) : b₂ =[p₂] b₃.
  change_path !inv_con_cancel_left (q @o r)

Definition pathover_cancel_left' (q : b =[p] b₂) (r : b₂ =[p^-1 @ p₁₃] b₃) : b =[p₁₃] b₃.
  change_path !con_inv_cancel_left (q @o r)

  (* Some of theDefinitions analogous toDefinitions for = in init.path *)

Definition cono_idpo (r : b =[p] b₂) : r @o idpo = r.
  by reflexivity

Definition idpo_cono (r : b =[p] b₂) : idpo @o r =[idp_con p] r.
  by induction r; constructor

Definition cono.assoc' (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) (r₃ : b₃ =[p₃] b₄) :
    r @o (r₂ @o r₃) =[(concat_pp_p _ _ _)'] (r @o r₂) @o r₃.
  by induction r₃; constructor

Definition cono.assoc (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) (r₃ : b₃ =[p₃] b₄) :
    (r @o r₂) @o r₃ =[(concat_pp_p _ _ _)] r @o (r₂ @o r₃).
  by induction r₃; constructor

Definition cono.right_inv (r : b =[p] b₂) : r @o r^-1ᵒ =[(con_pV _)] idpo.
  by induction r; constructor

Definition cono.left_inv (r : b =[p] b₂) : r^-1ᵒ @o r =[(con_Vp _)] idpo.
  by induction r; constructor

Definition eq_of_pathover {a' a₂' : A'} (q : a' =[p] a₂') : a' = a₂'.
  by cases q;reflexivity

Definition pathover_of_eq [unfold 5 8] (p : a = a₂) {a' a₂' : A'} (q : a' = a₂') : a' =[p] a₂'.
  by cases p;cases q;constructor

Definition pathover_constant (p : a = a₂) (a' a₂' : A') : a' =[p] a₂' <~> a' = a₂'.
Proof.
    fapply equiv.MK,
    { exact eq_of_pathover},
    { exact pathover_of_eq p},
    { intro r, cases p, cases r, reflexivity},
    { intro r, cases r, reflexivity},
Defined.

Definition pathover_of_eq_tr_constant_inv (p : a = a₂) (a' : A')
    : pathover_of_eq p (tr_constant p a')^-1 = pathover_tr p a'.
  by cases p; constructor

Definition eq_of_pathover_idp {b' : B a} (q : b =[idpath a] b') : b = b'.
  tr_eq_of_pathover q

  --should B be explicit in the next twoDefinitions?
Definition pathover_idp_of_eq {b' : B a} (q : b = b') : b =[idpath a] b'.
  pathover_of_tr_eq q

Definition pathover_idp (b : B a) (b' : B a) : b =[idpath a] b' <~> b = b'.
  equiv.MK eq_of_pathover_idp
           (pathover_idp_of_eq)
           (to_right_inv !pathover_equiv_tr_eq)
           (to_left_inv !pathover_equiv_tr_eq)

Definition eq_of_pathover_idp_pathover_of_eq {A X : Type} (x : X) {a a' : A} (p : a = a') :
    eq_of_pathover_idp (pathover_of_eq (idpath x) p) = p.
  by induction p; reflexivity

  variable (B)
Definition idpo_concato_eq (r : b = b') : eq_of_pathover_idp (@idpo A B a b @op r) = r.
  by induction r; reflexivity
  variable {B}

  (*Definition pathover_idp (b : B a) (b' : B a) : b =[idpath a] b' <~> b = b' . *)
  (* pathover_equiv_tr_eq idp b b' *)

  (*Definition eq_of_pathover_idp {b' : B a} (q : b =[idpath a] b') : b = b' . *)
  (* to_fun !pathover_idp q *)

  (*Definition pathover_idp_of_eq {b' : B a} (q : b = b') : b =[idpath a] b' . *)
  (* to_inv !pathover_idp q *)

Definition idp_rec_on [recursor] {P : forall (b₂ : B a), b =[idpath a] b₂ -> Type}
    {b₂ : B a} (r : b =[idpath a] b₂) (H : P idpo) : P r.
  have H2 : P (pathover_idp_of_eq (eq_of_pathover_idp r)), from
    eq.rec_on (eq_of_pathover_idp r) H,
  proof left_inv !pathover_idp r # H2 qed

Definition rec_on_right [recursor] {P : forall (b₂ : B a₂), b =[p] b₂ -> Type}
    {b₂ : B a₂} (r : b =[p] b₂) (H : P !pathover_tr) : P r.
  by cases r; exact H

Definition rec_on_left [recursor] {P : forall (b : B a), b =[p] b₂ -> Type}
    {b : B a} (r : b =[p] b₂) (H : P !tr_pathover) : P r.
  by cases r; exact H

  --pathover with fibration B' o f
Definition pathover_ap [unfold 10] (B' : A' -> Type) (f : A -> A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) : b =[ap f p] b₂.
  by cases q; constructor

Definition pathover_of_pathover_ap (B' : A' -> Type) (f : A -> A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[ap f p] b₂) : b =[p] b₂.
  by cases p; apply (idp_rec_on q); apply idpo

Definition pathover_compose (B' : A' -> Type) (f : A -> A') (p : a = a₂)
    (b : B' (f a)) (b₂ : B' (f a₂)) : b =[p] b₂ <~> b =[ap f p] b₂.
Proof.
    fapply equiv.MK,
    { exact pathover_ap B' f},
    { exact pathover_of_pathover_ap B' f},
    { intro q, cases p, esimp, apply (idp_rec_on q), apply idp},
    { intro q, cases q, reflexivity},
Defined.

Definition pathover_of_pathover_tr (q : b =[p @ p₂] p₂ # b₂) : b =[p] b₂.
  pathover_cancel_right q !pathover_tr^-1ᵒ

Definition pathover_tr_of_pathover (q : b =[p₁₃ @ p₂^-1] b₂) : b =[p₁₃] p₂ # b₂.
  pathover_cancel_right' q !pathover_tr

Definition pathover_of_tr_pathover (q : p # b =[p^-1 @ p₁₃] b₃) : b =[p₁₃] b₃.
  pathover_cancel_left' !pathover_tr q

Definition tr_pathover_of_pathover (q : b =[p @ p₂] b₃) : p # b =[p₂] b₃.
  pathover_cancel_left !pathover_tr^-1ᵒ q

Definition pathover_tr_of_eq (q : b = b') : b =[p] p # b'.
  by cases q;apply pathover_tr

Definition tr_pathover_of_eq (q : b₂ = b₂') : p^-1 # b₂ =[p] b₂'.
  by cases q;apply tr_pathover

Definition eq_of_parallel_po_right (q : b =[p] b₂) (q' : b =[p] b₂') : b₂ = b₂'.
Proof.
    apply @eq_of_pathover_idp A B, apply change_path (con.left_inv p),
    exact q^-1ᵒ @o q'
Defined.

Definition eq_of_parallel_po_left (q : b =[p] b₂) (q' : b' =[p] b₂) : b = b'.
Proof.
    apply @eq_of_pathover_idp A B, apply change_path (con.right_inv p),
    exact q @o q'^-1ᵒ
Defined.

  variable (C)
Definition transporto (r : b =[p] b₂) (c : C b) : C b₂.
  by induction r;exact c
  infix ` ▸o `:75 . transporto _

Definition fn_tro_eq_tro_fn {C' : forall (a : A), B a -> Type} (q : b =[p] b₂)
    (f : forall (a : A) (b : B a), C b -> C' b) (c : C b) : f b₂ (q ▸o c) = q ▸o (f b c).
  by induction q; reflexivity
  variable {C}

  (* various variants of ap for pathovers *)
Definition apd (f : forall a, B a) (p : a = a₂) : f a =[p] f a₂.
  by induction p; constructor

Definition apd_idp [unfold_full] (f : forall a, B a) : apd f idp = @idpo A B a (f a).
  by reflexivity

Definition apo [unfold 12] {f : A -> A'} (g : forall a, B a -> B'' (f a)) (q : b =[p] b₂) :
    g a b =[p] g a₂ b₂.
  by induction q; constructor

Definition apd011 [unfold 10] (f : forall a, B a -> A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
      : f a b = f a₂ b₂.
  by cases Hb; reflexivity

Definition apd0111 [unfold 13 14] (f : forall a b, C b -> A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
    (Hc : c =[apd011 C Ha Hb] c₂) : f a b c = f a₂ b₂ c₂.
  by cases Hb; apply (idp_rec_on Hc); apply idp

Definition apod11 {f : forall b, C b} {g : forall b₂, C b₂} (r : f =[p] g)
    {b : B a} {b₂ : B a₂} (q : b =[p] b₂) : f b =[apd011 C p q] g b₂.
  by cases r; apply (idp_rec_on q); constructor

Definition apdo10 {f : forall b, C b} {g : forall b₂, C b₂} (r : f =[p] g)
    (b : B a) : f b =[apd011 C p !pathover_tr] g (p # b).
  by cases r; constructor

Definition apo10 {f : B a -> B' a} {g : B a₂ -> B' a₂} (r : f =[p] g)
    (b : B a) : f b =[p] g (p # b).
  by cases r; constructor

Definition apo10_constant_right {f : B a -> A'} {g : B a₂ -> A'} (r : f =[p] g)
    (b : B a) : f b = g (p # b).
  by cases r; constructor

Definition apo10_constant_left {f : A' -> B a} {g : A' -> B a₂} (r : f =[p] g)
    (a' : A') : f a' =[p] g a'.
  by cases r; constructor

Definition apo11 {f : B a -> B' a} {g : B a₂ -> B' a₂} (r : f =[p] g)
    (q : b =[p] b₂) : f b =[p] g b₂.
  by induction q; exact apo10 r b

Definition apo011 {A : Type} {B C D : A -> Type} {a a' : A} {p : a = a'} {b : B a} {b' : B a'}
    {c : C a} {c' : C a'} (f : forall (a), B a -> C a -> D a) (q : b =[p] b') (r : c =[p] c') :
    f b c =[p] f b' c'.
Proof. induction q, induction r using idp_rec_on, exact idpo end

Definition apdo011 {A : Type} {B : A -> Type} {C : forall (a), B a -> Type}
    (f : forall (a) (b : B a), C b) {a a' : A} (p : a = a') {b : B a} {b' : B a'} (q : b =[p] b')
      : f b =[apd011 C p q] f b'.
  by cases q; constructor

Definition apdo0111 {A : Type} {B : A -> Type} {C C' : forall (a), B a -> Type}
    (f : forall (a) {b : B a}, C b -> C' b) {a a' : A} (p : a = a') {b : B a} {b' : B a'} (q : b =[p] b')
    {c : C b} {c' : C b'} (r : c =[apd011 C p q] c')
      : f c =[apd011 C' p q] f c'.
Proof.
    induction q, esimp at r, induction r using idp_rec_on, constructor
Defined.

Definition apo11_constant_right [unfold 12] {f : B a -> A'} {g : B a₂ -> A'}
    (q : f =[p] g) (r : b =[p] b₂) : f b = g b₂.
  eq_of_pathover (apo11 q r)

  (* properties about these "ap"s, transporto and pathover_ap *)
Definition apd_con (f : forall a, B a) (p : a = a₂) (q : a₂ = a₃)
    : apd f (p @ q) = apd f p @o apd f q.
  by cases p; cases q; reflexivity

Definition apd_inv (f : forall a, B a) (p : a = a₂) : apd f p^-1 = (apd f p)^-1ᵒ.
  by cases p; reflexivity

Definition apd_eq_pathover_of_eq_ap (f : A -> A') (p : a = a₂) :
    apd f p = pathover_of_eq p (ap f p).
  eq.rec_on p idp

Definition apo_invo (f : forall a, B a -> B' a) {Ha : a = a₂} (Hb : b =[Ha] b₂)
      : (apo f Hb)^-1ᵒ = apo f Hb^-1ᵒ.
  by induction Hb; reflexivity

Definition apd011_inv (f : forall a, B a -> A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
      : (apd011 f Ha Hb)^-1 = (apd011 f Ha^-1 Hb^-1ᵒ).
  by induction Hb; reflexivity

Definition cast_apd011 (q : b =[p] b₂) (c : C b) : cast (apd011 C p q) c = q ▸o c.
  by induction q; reflexivity

Definition apd_compose1 (g : forall a, B a -> B' a) (f : forall a, B a) (p : a = a₂)
    : apd (g o' f) p = apo g (apd f p).
  by induction p; reflexivity

Definition apd_compose2 (g : forall a', B'' a') (f : A -> A') (p : a = a₂)
    : apd (fun a => g (f a)) p = pathover_of_pathover_ap B'' f (apd g (ap f p)).
  by induction p; reflexivity

Definition apo_tro (C : forall (a), B' a -> Type) (f : forall (a), B a -> B' a) (q : b =[p] b₂)
    (c : C (f b)) : apo f q ▸o c = q ▸o c.
  by induction q; reflexivity

Definition pathover_ap_tro {B' : A' -> Type} (C : forall (a'), B' a' -> Type) (f : A -> A')
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) (c : C b) : pathover_ap B' f q ▸o c = q ▸o c.
  by induction q; reflexivity

Definition pathover_ap_invo_tro {B' : A' -> Type} (C : forall (a'), B' a' -> Type) (f : A -> A')
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) (c : C b₂)
    : (pathover_ap B' f q)^-1ᵒ ▸o c = q^-1ᵒ ▸o c.
  by induction q; reflexivity

Definition pathover_tro (q : b =[p] b₂) (c : C b) : c =[apd011 C p q] q ▸o c.
  by induction q; constructor

Definition pathover_ap_invo {B' : A' -> Type} (f : A -> A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂)
    : pathover_ap B' f q^-1ᵒ =[ap_inv f p] (pathover_ap B' f q)^-1ᵒ.
  by induction q; exact idpo

Definition tro_invo_tro {A : Type} {B : A -> Type} (C : forall (a), B a -> Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') (c : C b') :
    q ▸o (q^-1ᵒ ▸o c) = c.
  by induction q; reflexivity

Definition invo_tro_tro {A : Type} {B : A -> Type} (C : forall (a), B a -> Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') (c : C b) :
    q^-1ᵒ ▸o (q ▸o c) = c.
  by induction q; reflexivity

Definition cono_tro {A : Type} {B : A -> Type} (C : forall (a), B a -> Type)
    {a₁ a₂ a₃ : A} {p₁ : a₁ = a₂} {p₂ : a₂ = a₃} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (q₁ : b₁ =[p₁] b₂) (q₂ : b₂ =[p₂] b₃) (c : C b₁) :
    transporto C (q₁ @o q₂) c = transporto C q₂ (transporto C q₁ c).
  by induction q₂; reflexivity

Definition is_equiv_transporto {A : Type} {B : A -> Type} (C : forall (a), B a -> Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') : is_equiv (transporto C q).
Proof.
    fapply adjointify,
    { exact transporto C q^-1ᵒ},
    { exact tro_invo_tro C q},
    { exact invo_tro_tro C q}
Defined.

Definition equiv_apd011 {A : Type} {B : A -> Type} (C : forall (a), B a -> Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') : C b <~> C b'.
  equiv.mk (transporto C q) !is_equiv_transporto

  (* some cancellation laws for concato_eq an variants *)

Definition cono.right_inv_eq (q : b = b') :
    pathover_idp_of_eq q @op q^-1 = (idpo : b =[refl a] b).
  by induction q; constructor

Definition cono.right_inv_eq' (q : b = b') :
    q @po (pathover_idp_of_eq q^-1) = (idpo : b =[refl a] b).
  by induction q; constructor

Definition cono.left_inv_eq (q : b = b') :
    pathover_idp_of_eq q^-1 @op q = (idpo : b' =[refl a] b').
  by induction q; constructor

Definition cono.left_inv_eq' (q : b = b') :
    q^-1 @po pathover_idp_of_eq q = (idpo : b' =[refl a] b').
  by induction q; constructor

Definition pathover_of_fn_pathover_fn (f : forall {a}, B a <~> B' a) (r : f b =[p] f b₂) : b =[p] b₂.
  (left_inv f b)^-1 @po apo (fun a => f^-1ᵉ) r @op left_inv f b₂

  (* a pathover in a pathover type where the only thing which varies is the path is the same as
    an equality with a change_path *)
Definition change_path_of_pathover (s : p = p') (r : b =[p] b₂) (r' : b =[p'] b₂)
    (q : r =[s] r') : change_path s r = r'.
  by induction s; eapply idp_rec_on q; reflexivity

Definition pathover_of_change_path (s : p = p') (r : b =[p] b₂) (r' : b =[p'] b₂)
    (q : change_path s r = r') : r =[s] r'.
  by induction s; induction q; constructor

Definition pathover_pathover_path (s : p = p') (r : b =[p] b₂) (r' : b =[p'] b₂) :
    (r =[s] r') <~> change_path s r = r'.
Proof.
    fapply equiv.MK,
    { apply change_path_of_pathover},
    { apply pathover_of_change_path},
    { intro q, induction s, induction q, reflexivity},
    { intro q, induction s, eapply idp_rec_on q, reflexivity},
Defined.

  (* variants of inverse2 and concat2 *)
Definition inverseo2 [unfold 10] {r r' : b =[p] b₂} (s : r = r') : r^-1ᵒ = r'^-1ᵒ.
  by induction s; reflexivity

Definition concato2 [unfold 15 16] {r r' : b =[p] b₂} {r₂ r₂' : b₂ =[p₂] b₃}
    (s : r = r') (s₂ : r₂ = r₂') : r @o r₂ = r' @o r₂'.
  by induction s; induction s₂; reflexivity

  infixl ` ◾o `:75 . concato2
  postfix [parsing_only] `⁻²ᵒ`:(max+10) . inverseo2 --this notation is abusive, should we use it?

  (* find a better name for this *)
Definition fn_tro_eq_tro_fn2 (q : b =[p] b₂)
    {k : A -> A} {l : forall (a), B a -> B (k a)} (m : forall (a) {b : B a}, C b -> C (l b))
    (c : C b) :
    m (q ▸o c) = (pathover_ap B k (apo l q)) ▸o (m c).
  by induction q; reflexivity

Definition apd0111_precompose (f  : forall (a) {b : B a}, C b -> A')
    {k : A -> A} {l : forall (a), B a -> B (k a)} (m : forall (a) {b : B a}, C b -> C (l b))
    {q : b =[p] b₂} (c : C b)
    : apd0111 (fun a b c => f (m c)) p q (pathover_tro q c) @ ap (@f _ _) (fn_tro_eq_tro_fn2 q m c) =
      apd0111 f (ap k p) (pathover_ap B k (apo l q)) (pathover_tro _ (m c)).
  by induction q; reflexivity

Defined. eq
