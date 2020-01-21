(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

General properties of binary operations.
*)
open eq.ops function

namespace binary
  section
  variable {A : Type}
  variables (op₁ : A -> A -> A) (inv : A -> A) (one : A)

  local notation a * b . op₁ a b
  local notation a ^-1  . inv a

Definition commutative        . forall a b, a * b = b * a
Definition associative        . forall a b c, (a * b) * c = a * (b * c)
Definition left_identity      . forall a, one * a = a
Definition right_identity     . forall a, a * one = a
Definition left_inverse       . forall a, a^-1 * a = one
Definition right_inverse      . forall a, a * a^-1 = one
Definition left_cancelative   . forall a b c, a * b = a * c -> b = c
Definition right_cancelative  . forall a b c, a * b = c * b -> a = c

Definition inv_op_cancel_left  . forall a b, a^-1 * (a * b) = b
Definition op_inv_cancel_left  . forall a b, a * (a^-1 * b) = b
Definition inv_op_cancel_right  . forall a b, a * b^-1 * b =  a
Definition op_inv_cancel_right  . forall a b, a * b * b^-1 = a

  variable (op₂ : A -> A -> A)

  local notation a + b . op₂ a b

Definition left_distributive  . forall a b c, a * (b + c) = a * b + a * c
Definition right_distributive  . forall a b c, (a + b) * c = a * c + b * c

Definition right_commutative  {B : Type} (f : B -> A -> B) . forall b a₁ a₂, f (f b a₁) a₂ = f (f b a₂) a₁
Definition left_commutative  {B : Type}  (f : A -> B -> B) . forall a₁ a₂ b, f a₁ (f a₂ b) = f a₂ (f a₁ b)
Defined.

  section
  variable {A : Type}
  variable {f : A -> A -> A}
  variable H_comm : commutative f
  variable H_assoc : associative f
  local infixl `*` . f
Definition left_comm : left_commutative f.
  take a b c, calc
  a*(b*c) = (a*b)*c  : H_assoc
  ...   = (b*a)*c  : H_comm
  ...   = b*(a*c)  : H_assoc

Definition right_comm : right_commutative f.
  take a b c, calc
  (a*b)*c = a*(b*c) : H_assoc
  ...   = a*(c*b) : H_comm
  ...   = (a*c)*b : H_assoc

Definition comm4 (a b c d : A) : a*b*(c*d) = a*c*(b*d).
  calc
  a*b*(c*d) = a*b*c*d   : H_assoc
  ...     = a*c*b*d   : right_comm H_comm H_assoc
  ...     = a*c*(b*d) : H_assoc
Defined.

  section
  variable {A : Type}
  variable {f : A -> A -> A}
  variable H_assoc : associative f
  local infixl `*` . f
Definition assoc4helper (a b c d) : (a*b)*(c*d) = a*((b*c)*d).
  calc
  (a*b)*(c*d) = a*(b*(c*d)) : H_assoc
  ... = a*((b*c)*d) : H_assoc
Defined.

Definition right_commutative_compose_right
  {A B : Type} (f : A -> A -> A) (g : B -> A) (rcomm : right_commutative f) : right_commutative (compose_right f g).
  fun a b₁ b₂ => !rcomm

Definition left_commutative_compose_left
  {A B : Type} (f : A -> A -> A) (g : B -> A) (lcomm : left_commutative f) : left_commutative (compose_left f g).
  fun a b₁ b₂ => !lcomm
Defined. binary

open eq
namespace is_equiv
Definition inv_preserve_binary {A B : Type} (f : A -> B) [H : is_equiv f]
  (mA : A -> A -> A) (mB : B -> B -> B) (H : forall (a a' : A), f (mA a a') = mB (f a) (f a'))
  (b b' : B) : f^-1 (mB b b') = mA (f^-1 b) (f^-1 b').
Proof.
  have H2 : f^-1 (mB (f (f^-1 b)) (f (f^-1 b'))) = f^-1 (f (mA (f^-1 b) (f^-1 b'))), from ap f^-1 !H^-1,
  rewrite [+right_inv f at H2,left_inv f at H2,▸* at H2,H2]
Defined.

Definition preserve_binary_of_inv_preserve {A B : Type} (f : A -> B) [H : is_equiv f]
  (mA : A -> A -> A) (mB : B -> B -> B) (H : forall (b b' : B), f^-1 (mB b b') = mA (f^-1 b) (f^-1 b'))
  (a a' : A) : f (mA a a') = mB (f a) (f a').
Proof.
  have H2 : f (mA (f^-1 (f a)) (f^-1 (f a'))) = f (f^-1 (mB (f a) (f a'))), from ap f !H^-1,
  rewrite [right_inv f at H2,+left_inv f at H2,▸* at H2,H2]
Defined.
Defined. is_equiv
namespace equiv
  open is_equiv
Definition inv_preserve_binary {A B : Type} (f : A <~> B)
  (mA : A -> A -> A) (mB : B -> B -> B) (H : forall (a a' : A), f (mA a a') = mB (f a) (f a'))
  (b b' : B) : f^-1 (mB b b') = mA (f^-1 b) (f^-1 b').
  inv_preserve_binary f mA mB H b b'

Definition preserve_binary_of_inv_preserve {A B : Type} (f : A <~> B)
  (mA : A -> A -> A) (mB : B -> B -> B) (H : forall (b b' : B), f^-1 (mB b b') = mA (f^-1 b) (f^-1 b'))
  (a a' : A) : f (mA a a') = mB (f a) (f a').
  preserve_binary_of_inv_preserve f mA mB H a a'
Defined. equiv
