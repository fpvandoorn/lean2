/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the primitive hits in Lean
-/

prelude

import .trunc .pathover

open is_trunc eq list

/-
  We take two higher inductive types (hits) as primitive notions in Lean. We define all other hits
  in terms of these two hits. The hits which are primitive are
    - n-truncation
    - quotients (not truncated)
  For each of the hits we add the following constants:
    - the type formation
    - the term and path constructors
    - the dependent recursor
  We add the computation rule for point constructors judgmentally to the kernel of Lean.
  The computation rules for the path constructors are added (propositionally) as axioms

  In this file we only define the dependent recursor. For the nondependent recursor and all other
  uses of these hits, see the folder ../hit/
-/

constant trunc.{u} (n : ℕ₋₂) (A : Type.{u}) : Type.{u}

namespace trunc
  constant tr {n : ℕ₋₂} {A : Type} (a : A) : trunc n A
  constant is_trunc_trunc (n : ℕ₋₂) (A : Type) : is_trunc n (trunc n A)

  attribute is_trunc_trunc [instance]

  protected constant rec {n : ℕ₋₂} {A : Type} {P : trunc n A → Type}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) : Πaa, P aa

  protected definition rec_on [reducible] {n : ℕ₋₂} {A : Type}
    {P : trunc n A → Type} (aa : trunc n A) [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a))
    : P aa :=
  trunc.rec H aa
end trunc

constant quotient.{u v} {A : Type.{u}} (R : A → A → Type.{v}) : Type.{max u v}

namespace quotient

  constant class_of {A : Type} (R : A → A → Type) (a : A) : quotient R

  constant eq_of_rel {A : Type} (R : A → A → Type) ⦃a a' : A⦄ (H : R a a')
    : class_of R a = class_of R a'

  protected constant rec {A : Type} {R : A → A → Type} {P : quotient R → Type}
    (Pc : Π(a : A), P (class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a')
    (x : quotient R) : P x

  protected definition rec_on [reducible] {A : Type} {R : A → A → Type} {P : quotient R → Type}
    (x : quotient R) (Pc : Π(a : A), P (class_of R a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a') : P x :=
  quotient.rec Pc Pp x

end quotient

constant recursive_hit_family.{u v w} {A : Type.{u}} {R : list A → A → Type.{v}}
  (Q : Π⦃l l' : list A⦄ ⦃a : A⦄, R l a → R l' a → Type.{w}) : A → Type.{max u v w}

namespace recursive_hit_family

  constant incl {A : Type} {R : list A → A → Type} (Q : Π⦃l l' : list A⦄ ⦃a : A⦄, R l a → R l' a → Type) {l : list A} {a : A}
    (p : R l a) (x : prods (recursive_hit_family Q) l) : recursive_hit_family Q a

  constant pth {A : Type} {R : list A → A → Type} {Q : Π⦃l l' : list A⦄ ⦃a : A⦄, R l a → R l' a → Type} {l l' : list A} {a : A}
    {p : R l a} {p' : R l' a} (q : Q p p') (x : prods (recursive_hit_family Q) l) (x' : prods (recursive_hit_family Q) l')
    : incl Q p x = incl Q p' x'

  protected constant rec {A : Type} {R : list A → A → Type} {Q : Π⦃l l' : list A⦄ ⦃a : A⦄, R l a → R l' a → Type}
    {P : Π⦃a⦄, recursive_hit_family Q a → Type}
    (P0 : Π⦃l : list A⦄ ⦃a : A⦄ (p : R l a) (x : prods (recursive_hit_family Q) l) (ps : dprods P l x), P (incl Q p x))
    (P1 : Π⦃l l' : list A⦄ ⦃a : A⦄ {p : R l a} {p' : R l' a} (q : Q p p') (x : prods (recursive_hit_family Q) l)
      (x' : prods (recursive_hit_family Q) l') (ps : dprods P l x) (ps' : dprods P l' x'), P0 p x ps =[pth q x x'] P0 p' x' ps')
    {a : A} (x : recursive_hit_family Q a) : P x

end recursive_hit_family

init_hits -- Initialize builtin computational rules for trunc and quotient

namespace trunc
  definition rec_tr [reducible] {n : ℕ₋₂} {A : Type} {P : trunc n A → Type}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) (a : A) : trunc.rec H (tr a) = H a :=
  idp
end trunc

namespace quotient
  definition rec_class_of {A : Type} {R : A → A → Type} {P : quotient R → Type}
    (Pc : Π(a : A), P (class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a')
    (a : A) : quotient.rec Pc Pp (class_of R a) = Pc a :=
  idp

  constant rec_eq_of_rel {A : Type} {R : A → A → Type} {P : quotient R → Type}
    (Pc : Π(a : A), P (class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a')
    {a a' : A} (H : R a a') : apd (quotient.rec Pc Pp) (eq_of_rel R H) = Pp H
end quotient

attribute quotient.class_of trunc.tr recursive_hit_family.incl [constructor]
attribute quotient.rec_on trunc.rec_on [unfold 4]
