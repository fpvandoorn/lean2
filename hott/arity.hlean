(*
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about functions with multiple arguments
*)

variables {A U V W X Y Z : Type} {B : A -> Type} {C : forall a, B a -> Type} {D : forall a b, C a b -> Type}
  {E : forall a b c, D a b c -> Type} {F : forall a b c d, E a b c d -> Type}
  {G : forall a b c d e, F a b c d e -> Type} {H : forall a b c d e f, G a b c d e f -> Type}
variables {a a' : A} {u u' : U} {v v' : V} {w w' : W} {x x' x'' : X} {y y' : Y} {z z' : Z}
  {b : B a} {b' : B a'}
  {c : C a b} {c' : C a' b'}
  {d : D a b c} {d' : D a' b' c'}
  {e : E a b c d} {e' : E a' b' c' d'}
  {ff : F a b c d e} {f' : F a' b' c' d' e'}
  {g : G a b c d e ff} {g' : G a' b' c' d' e' f'}
  {h : H a b c d e ff g} {h' : H a' b' c' d' e' f' g'}

namespace eq
  (*
  Naming convention:
  TheDefinition which states how to construct an path between two function applications is
  api₀i₁...iₙ.
  Here i₀, ... iₙ are digits, n is the arity of the function(s) =>
  and iⱼ specifies the dimension of the path between the jᵗʰ argument
  (i₀ specifies the dimension of the path between the functions).
  A value iⱼ ≡ 0 means that the jᵗʰ arguments areDefinitionally equal
  The functions are non-dependent => except when theDefinition name contains trailing zeroes
  (where the function is dependent only in the arguments where it doesn't result in any
  transports in theDefinition statement).
  For the fully-dependent versions (except that the conclusion doesn't contain a transport)
  we write
  apdi₀i₁...iₙ.

  For versions where only some arguments depend on some other arguments,
  or for versions with transport in the conclusion (like apdt), we don't have a
  consistent naming scheme (yet).

  We don't prove eachDefinition systematically, but prove only the ones which we actually need.
  *)

Definition homotopy2 (f g : forall a b, C a b)         : Type.
  forall a b, f a b = g a b
Definition homotopy3 (f g : forall a b c, D a b c)     : Type.
  forall a b c, f a b c = g a b c
Definition homotopy4 (f g : forall a b c d, E a b c d) : Type.
  forall a b c d, f a b c d = g a b c d

  infix ` ~2 `:50 . homotopy2
  infix ` ~3 `:50 . homotopy3

Definition ap0111 (f : U -> V -> W -> X) (Hu : u = u') (Hv : v = v') (Hw : w = w')
  : f u v w = f u' v' w'.
  by cases Hu; congruence; repeat assumption

Definition ap01111 (f : U -> V -> W -> X -> Y)
  (Hu : u = u') (Hv : v = v') (Hw : w = w') (Hx : x = x')
  : f u v w x = f u' v' w' x'.
  by cases Hu; congruence; repeat assumption

Definition ap011111 (f : U -> V -> W -> X -> Y -> Z)
  (Hu : u = u') (Hv : v = v') (Hw : w = w') (Hx : x = x') (Hy : y = y')
  : f u v w x y = f u' v' w' x' y'.
  by cases Hu; congruence; repeat assumption

Definition ap0111111 (f : U -> V -> W -> X -> Y -> Z -> A)
  (Hu : u = u') (Hv : v = v') (Hw : w = w') (Hx : x = x') (Hy : y = y') (Hz : z = z')
  : f u v w x y z = f u' v' w' x' y' z'.
  by cases Hu; congruence; repeat assumption

Definition ap010 (f : X -> forall a, B a) (Hx : x = x') : f x == f x'.
  by intros; cases Hx; reflexivity

Definition ap0100 (f : X -> forall a b, C a b) (Hx : x = x') : f x ~2 f x'.
  by intros; cases Hx; reflexivity

Definition ap01000 (f : X -> forall a b c, D a b c) (Hx : x = x') : f x ~3 f x'.
  by intros; cases Hx; reflexivity

Definition apdt011 (f : forall a, B a -> Z) (Ha : a = a') (Hb : transport B Ha b = b')
  : f a b = f a' b'.
  by cases Ha; cases Hb; reflexivity

Definition apdt0111 (f : forall a b, C a b -> Z) (Ha : a = a') (Hb : transport B Ha b = b')
  (Hc : cast (apdt011 C Ha Hb) c = c')
  : f a b c = f a' b' c'.
  by cases Ha; cases Hb; cases Hc; reflexivity

Definition apdt01111 (f : forall a b c, D a b c -> Z) (Ha : a = a') (Hb : transport B Ha b = b')
  (Hc : cast (apdt011 C Ha Hb) c = c') (Hd : cast (apdt0111 D Ha Hb Hc) d = d')
  : f a b c d = f a' b' c' d'.
  by cases Ha; cases Hb; cases Hc; cases Hd; reflexivity

Definition apdt011111 (f : forall a b c d, E a b c d -> Z) (Ha : a = a') (Hb : transport B Ha b = b')
  (Hc : cast (apdt011 C Ha Hb) c = c') (Hd : cast (apdt0111 D Ha Hb Hc) d = d')
  (He : cast (apdt01111 E Ha Hb Hc Hd) e = e')
  : f a b c d e = f a' b' c' d' e'.
  by cases Ha; cases Hb; cases Hc; cases Hd; cases He; reflexivity

Definition apdt0111111 (f : forall a b c d e, F a b c d e -> Z) (Ha : a = a') (Hb : transport B Ha b = b')
  (Hc : cast (apdt011 C Ha Hb) c = c') (Hd : cast (apdt0111 D Ha Hb Hc) d = d')
  (He : cast (apdt01111 E Ha Hb Hc Hd) e = e') (Hf : cast (apdt011111 F Ha Hb Hc Hd He) ff = f')
  : f a b c d e ff = f a' b' c' d' e' f'.
Proof. cases Ha, cases Hb, cases Hc, cases Hd, cases He, cases Hf, reflexivity end

  (*Definition apd0111111 (f : forall a b c d e ff, G a b c d e ff -> Z) (Ha : a = a') (Hb : transport B Ha b = b') *)
  (*   (Hc : cast (apd011 C Ha Hb) c = c') (Hd : cast (apd0111 D Ha Hb Hc) d = d') *)
  (*   (He : cast (apd01111 E Ha Hb Hc Hd) e = e') (Hf : cast (apd011111 F Ha Hb Hc Hd He) ff = f') *)
  (*   (Hg : cast (apd0111111 G Ha Hb Hc Hd He Hf) g = g') *)
  (*   : f a b c d e ff g = f a' b' c' d' e' f' g' . *)
  (* by cases Ha; cases Hb; cases Hc; cases Hd; cases He; cases Hf; cases Hg; reflexivity *)

  (*Definition apd01111111 (f : forall a b c d e ff g, G a b c d e ff g -> Z) (Ha : a = a') (Hb : transport B Ha b = b') *)
  (*   (Hc : cast (apd011 C Ha Hb) c = c') (Hd : cast (apd0111 D Ha Hb Hc) d = d') *)
  (*   (He : cast (apd01111 E Ha Hb Hc Hd) e = e') (Hf : cast (apd011111 F Ha Hb Hc Hd He) ff = f') *)
  (*   (Hg : cast (apd0111111 G Ha Hb Hc Hd He Hf) g = g') (Hh : cast (apd01111111 H Ha Hb Hc Hd He Hf Hg) h = h') *)
  (*   : f a b c d e ff g h = f a' b' c' d' e' f' g' h' . *)
  (* by cases Ha; cases Hb; cases Hc; cases Hd; cases He; cases Hf; cases Hg; cases Hh; reflexivity *)

Definition apd100 {f g : forall a b, C a b} (p : f = g) : f ~2 g.
  fun a b => apd10 (apd10 p a) b

Definition apd1000 {f g : forall a b c, D a b c} (p : f = g) : f ~3 g.
  fun a b c => apd100 (apd10 p a) b c

  (* some properties of these variants of ap *)

  (* we only prove what we currently need *)

Definition ap010_con (f : X -> forall a, B a) (p : x = x') (q : x' = x'') :
  ap010 f (p @ q) a = ap010 f p a @ ap010 f q a.
  eq.rec_on q (eq.rec_on p idp)

Definition ap010_ap (f : X -> forall a, B a) (g : Y -> X) (p : y = y') :
  ap010 f (ap g p) a = ap010 (fun y => f (g y)) p a.
  eq.rec_on p idp

Definition ap_eq_ap010 {A B C : Type} (f : A -> B -> C) {a a' : A} (p : a = a') (b : B) :
  ap (fun a => f a b) p = ap010 f p b.
  by reflexivity

Definition ap011_idp {A B C : Type} (f : A -> B -> C) {a a' : A} (p : a = a') (b : B) :
  ap011 f p idp = ap010 f p b.
  by reflexivity

Definition ap011_flip {A B C : Type} (f : A -> B -> C) {a a' : A} {b b' : B} (p : a = a') (q : b = b') :
  ap011 f p q = ap011 (fun b a => f a b) q p.
  by induction q; induction p; reflexivity

  (* the followingDefinitions are function extentionality for functions with multiple arguments *)

Definition eq_of_homotopy2 {f g : forall a b, C a b} (H : f ~2 g) : f = g.
  eq_of_homotopy (fun a => eq_of_homotopy (H a))

Definition eq_of_homotopy3 {f g : forall a b c, D a b c} (H : f ~3 g) : f = g.
  eq_of_homotopy (fun a => eq_of_homotopy2 (H a))

Definition eq_of_homotopy2_id (f : forall a b, C a b)
  : eq_of_homotopy2 (fun a b => idpath (f a b)) = idpath f.
Proof.
  transitivity eq_of_homotopy (fun a => idpath (f a)),
  {apply (ap eq_of_homotopy), apply eq_of_homotopy, intros, apply eq_of_homotopy_idp},
  apply eq_of_homotopy_idp
Defined.

Definition eq_of_homotopy3_id (f : forall a b c, D a b c)
  : eq_of_homotopy3 (fun a b c => idpath (f a b c)) = idpath f.
Proof.
  transitivity _,
  {apply (ap eq_of_homotopy), apply eq_of_homotopy, intros, apply eq_of_homotopy2_id},
  apply eq_of_homotopy_idp
Defined.

Definition eq_of_homotopy2_inv {f g : forall a b, C a b} (H : f ~2 g)
  : eq_of_homotopy2 (fun a b => (H a b)^-1) = (eq_of_homotopy2 H)^-1.
  ap eq_of_homotopy (eq_of_homotopy (fun a => !eq_of_homotopy_inv)) @ !eq_of_homotopy_inv

Definition eq_of_homotopy3_inv {f g : forall a b c, D a b c} (H : f ~3 g)
  : eq_of_homotopy3 (fun a b c => (H a b c)^-1) = (eq_of_homotopy3 H)^-1.
  ap eq_of_homotopy (eq_of_homotopy (fun a => !eq_of_homotopy2_inv)) @ !eq_of_homotopy_inv

Definition eq_of_homotopy2_con {f g h : forall a b, C a b} (H1 : f ~2 g) (H2 : g ~2 h)
  : eq_of_homotopy2 (fun a b => H1 a b @ H2 a b) = eq_of_homotopy2 H1 @ eq_of_homotopy2 H2.
  ap eq_of_homotopy (eq_of_homotopy (fun a => !eq_of_homotopy_con)) @ !eq_of_homotopy_con

Definition eq_of_homotopy3_con {f g h : forall a b c, D a b c} (H1 : f ~3 g) (H2 : g ~3 h)
  : eq_of_homotopy3 (fun a b c => H1 a b c @ H2 a b c) = eq_of_homotopy3 H1 @ eq_of_homotopy3 H2.
  ap eq_of_homotopy (eq_of_homotopy (fun a => !eq_of_homotopy2_con)) @ !eq_of_homotopy_con

Defined. eq

open eq equiv is_equiv
namespace funext
Definition is_equiv_apd100 [instance] (f g : forall a b, C a b)
  : is_equiv (@apd100 A B C f g).
  adjointify _
  eq_of_homotopy2
Proof.
  intro H, esimp [apd100, eq_of_homotopy2],
  apply eq_of_homotopy, intro a,
  apply concat, apply (ap (fun x => apd10 (x a))), apply (right_inv apd10),
  apply (right_inv apd10)
Defined.
Proof.
  intro p, cases p, apply eq_of_homotopy2_id
Defined.

Definition is_equiv_apd1000 [instance] (f g : forall a b c, D a b c)
  : is_equiv (@apd1000 A B C D f g).
  adjointify _
  eq_of_homotopy3
Proof.
  intro H, esimp,
  apply eq_of_homotopy, intro a,
  transitivity apd100 (eq_of_homotopy2 (H a)),
  {apply ap (fun x => apd100 (x a)),
  apply right_inv apd10},
  apply right_inv apd100
Defined.
Proof.
  intro p, cases p, apply eq_of_homotopy3_id
Defined.
Defined. funext



namespace eq
  open funext
  local attribute funext.is_equiv_apd100 [instance]
  protectedDefinition homotopy2.rec_on {f g : forall a b, C a b} {P : (f ~2 g) -> Type}
  (p : f ~2 g) (H : forall (q : f = g), P (apd100 q)) : P p.
  right_inv apd100 p # H (eq_of_homotopy2 p)

  protectedDefinition homotopy3.rec_on {f g : forall a b c, D a b c} {P : (f ~3 g) -> Type}
  (p : f ~3 g) (H : forall (q : f = g), P (apd1000 q)) : P p.
  right_inv apd1000 p # H (eq_of_homotopy3 p)

Definition eq_equiv_homotopy2 (f g : forall a b, C a b) : (f = g) <~> (f ~2 g).
  equiv.mk apd100 _

Definition eq_equiv_homotopy3 (f g : forall a b c, D a b c) : (f = g) <~> (f ~3 g).
  equiv.mk apd1000 _

Definition apd10_ap (f : X -> forall a, B a) (p : x = x')
  : apd10 (ap f p) = ap010 f p.
  eq.rec_on p idp

Definition eq_of_homotopy_ap010 (f : X -> forall a, B a) (p : x = x')
  : eq_of_homotopy (ap010 f p) = ap f p.
  inv_eq_of_eq !apd10_ap^-1

Definition ap_eq_ap_of_homotopy {f : X -> forall a, B a} {p q : x = x'} (H : ap010 f p == ap010 f q)
  : ap f p = ap f q.
  calc
  ap f p = eq_of_homotopy (ap010 f p) : eq_of_homotopy_ap010
  ... = eq_of_homotopy (ap010 f q) : eq_of_homotopy H
  ... = ap f q                     : eq_of_homotopy_ap010

Defined. eq
