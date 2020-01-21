(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about sums/coproducts/disjoint unions
*)

import .pi .equiv logic

open lift eq is_equiv equiv prod prod.ops is_trunc sigma bool

namespace sum
  universe variables u v u' v'
  variables {A : Type.{u}} {B : Type.{v}} (z z' : A + B) {P : A -> Type.{u'}} {Q : A -> Type.{v'}}

  protectedDefinition eta : sum.rec inl inr z = z.
  by induction z; all_goals reflexivity

  protectedDefinition code [unfold 3 4] : A + B -> A + B -> Type.{max u v}
  | code (inl a) (inl a') . lift (a = a')
  | code (inr b) (inr b') . lift (b = b')
  | code _       _        . lift empty

  protectedDefinition decode [unfold 3 4] : forall (z z' : A + B), sum.code z z' -> z = z'
  | decode (inl a) (inl a') . fun c => ap inl (down c)
  | decode (inl a) (inr b') . fun c => empty.elim (down c) _
  | decode (inr b) (inl a') . fun c => empty.elim (down c) _
  | decode (inr b) (inr b') . fun c => ap inr (down c)

  protectedDefinition mem_cases : (Σ a, z = inl a) + (Σ b, z = inr b).
  by cases z with a b; exact inl ⟨a, idp⟩; exact inr ⟨b, idp⟩

  protectedDefinition eqrec {A B : Type} {C : A + B -> Type}
    (x : A + B) (cl : forall a, x = inl a -> C (inl a)) (cr : forall b, x = inr b -> C (inr b)) : C x.
  by cases x with a b; exact cl a idp; exact cr b idp

  variables {z z'}
  protectedDefinition encode [unfold 3 4 5] (p : z = z') : sum.code z z'.
  by induction p; induction z; all_goals exact up idp

  variables (z z')
Definition sum_eq_equiv : (z = z') <~> sum.code z z'.
  equiv.MK sum.encode
           !sum.decode
           abstract begin
             intro c, induction z with a b, all_goals induction z' with a' b',
             all_goals (esimp at *; induction c with c),
             all_goals induction c, (* c either has type empty or a path *)
             all_goals reflexivity
           end end
           abstract begin
             intro p, induction p, induction z, all_goals reflexivity
           end end

  section
  variables {a a' : A} {b b' : B}
Definition eq_of_inl_eq_inl (p : inl a = inl a' :> A + B) : a = a'.
  down (sum.encode p)
Definition eq_of_inr_eq_inr (p : inr b = inr b' :> A + B) : b = b'.
  down (sum.encode p)
Definition empty_of_inl_eq_inr (p : inl a = inr b) : empty . down (sum.encode p)
Definition empty_of_inr_eq_inl (p : inr b = inl a) : empty . down (sum.encode p)

  (* Transport *)

Definition sum_transport (p : a = a') (z : P a + Q a)
    : p # z = sum.rec (fun a => inl (p # a)) (fun b => inr (p # b)) z.
  by induction p; induction z; all_goals reflexivity

  (* Pathovers *)

Definition etao (p : a = a') (z : P a + Q a)
    : z =[p] sum.rec (fun a => inl (p # a)) (fun b => inr (p # b)) z.
  by induction p; induction z; all_goals constructor

  protectedDefinition codeo (p : a = a') : P a + Q a -> P a' + Q a' -> Type.{max u' v'}
  | codeo (inl x) (inl x') . lift.{u' v'} (x =[p] x')
  | codeo (inr y) (inr y') . lift.{v' u'} (y =[p] y')
  | codeo _       _        . lift empty

  protectedDefinition decodeo (p : a = a') : forall (z : P a + Q a) (z' : P a' + Q a'),
    sum.codeo p z z' -> z =[p] z'
  | decodeo (inl x) (inl x') . fun c => apo (fun a => inl) (down c)
  | decodeo (inl x) (inr y') . fun c => empty.elim (down c) _
  | decodeo (inr y) (inl x') . fun c => empty.elim (down c) _
  | decodeo (inr y) (inr y') . fun c => apo (fun a => inr) (down c)

  variables {z z'}
  protectedDefinition encodeo {p : a = a'} {z : P a + Q a} {z' : P a' + Q a'} (q : z =[p] z')
    : sum.codeo p z z'.
  by induction q; induction z; all_goals exact up idpo

  variables (z z')
Definition sum_pathover_equiv (p : a = a') (z : P a + Q a) (z' : P a' + Q a')
    : (z =[p] z') <~> sum.codeo p z z'.
  equiv.MK sum.encodeo
           !sum.decodeo
           abstract begin
             intro c, induction z with a b, all_goals induction z' with a' b',
             all_goals (esimp at *; induction c with c),
             all_goals induction c, (* c either has type empty or a pathover *)
             all_goals reflexivity
           end end
           abstract begin
             intro q, induction q, induction z, all_goals reflexivity
           end end
Defined.

  (* Functorial action *)

  variables {A' B' : Type} (f : A -> A') (g : B -> B')
Definition sum_functor : A + B -> A' + B'
  | sum_functor (inl a) . inl (f a)
  | sum_functor (inr b) . inr (g b)

  (* Equivalences *)

Definition is_equiv_sum_functor [instance] [Hf : is_equiv f] [Hg : is_equiv g]
    : is_equiv (sum_functor f g).
  adjointify (sum_functor f   g)
             (sum_functor f^-1 g^-1)
             abstract begin
               intro z, induction z,
               all_goals (esimp; (apply ap inl | apply ap inr); apply right_inv)
             end end
             abstract begin
               intro z, induction z,
               all_goals (esimp; (apply ap inl | apply ap inr); apply right_inv)
             end end

Definition sum_equiv_sum_of_is_equiv [Hf : is_equiv f] [Hg : is_equiv g]
    : A + B <~> A' + B'.
  equiv.mk _ (is_equiv_sum_functor f g)

Definition sum_equiv_sum (f : A <~> A') (g : B <~> B') : A + B <~> A' + B'.
  equiv.mk _ (is_equiv_sum_functor f g)

Definition sum_equiv_sum_left (g : B <~> B') : A + B <~> A + B'.
  sum_equiv_sum equiv.rfl g

Definition sum_equiv_sum_right (f : A <~> A') : A + B <~> A' + B.
  sum_equiv_sum f equiv.rfl

Definition flip : A + B -> B + A
  | flip (inl a) . inr a
  | flip (inr b) . inl b

Definition sum_comm_equiv (A B : Type) : A + B <~> B + A.
Proof.
    fapply equiv.MK,
      exact flip,
      exact flip,
      all_goals (intro z; induction z; all_goals reflexivity)
Defined.

Definition sum_assoc_equiv (A B C : Type) : A + (B + C) <~> (A + B) + C.
Proof.
    fapply equiv.MK,
      all_goals try (intro z; induction z with u v;
                     all_goals try induction u; all_goals try induction v),
      exact inl (inl u),
      exact inl (inr a),
      exact inr a,
      exact inl a,
      exact inr (inl a),
      exact inr (inr v),
      all_goals reflexivity
Defined.

Definition sum_empty_equiv (A : Type) : A + empty <~> A.
Proof.
    fapply equiv.MK,
    { intro z, induction z, assumption, contradiction},
    { exact inl},
    { intro a, reflexivity},
    { intro z, induction z, reflexivity, contradiction}
Defined.

Definition empty_sum_equiv (A : Type) : empty + A <~> A.
  !sum_comm_equiv @e !sum_empty_equiv

Definition bool_equiv_unit_sum_unit : bool <~> unit + unit.
Proof.
    fapply equiv.MK,
    { intro b, cases b, exact inl unit.star, exact inr unit.star },
    { intro s, cases s, exact bool.ff, exact bool.tt },
    { intro s, cases s, do 2 (cases a; reflexivity) },
    { intro b, cases b, do 2 reflexivity },
Defined.

Definition sum_prod_right_distrib (A B C : Type) :
    (A + B) \* C <~> (A \* C) + (B \* C).
Proof.
    fapply equiv.MK,
    { intro x, cases x with ab c, cases ab with a b, exact inl (a, c), exact inr (b, c) },
    { intro x, cases x with ac bc, cases ac with a c, exact (inl a, c),
      cases bc with b c, exact (inr b, c) },
    { intro x, cases x with ac bc, cases ac with a c, reflexivity, cases bc, reflexivity },
    { intro x, cases x with ab c, cases ab with a b, do 2 reflexivity }
Defined.

Definition sum_prod_left_distrib (A B C : Type) :
    A \* (B + C) <~> (A \* B) + (A \* C).
  calc A \* (B + C) <~> (B + C) \* A : prod_comm_equiv
               ... <~> (B \* A) + (C \* A) : sum_prod_right_distrib
               ... <~> (A \* B) + (C \* A) : sum_equiv_sum_right !prod_comm_equiv
               ... <~> (A \* B) + (A \* C) : sum_equiv_sum_left  !prod_comm_equiv

  section
  variables (H : unit + A <~> unit + B)
  include H

  open unit decidable sigma.ops

Definition unit_sum_equiv_cancel_map : A -> B.
Proof.
    intro a, cases sum.mem_cases (H (inr a)) with u b, rotate 1, exact b.1,
    cases u with u Hu, cases sum.mem_cases (H (inl ⋆)) with u' b, rotate 1, exact b.1,
    cases u' with u' Hu', exfalso, apply empty_of_inl_eq_inr,
    calc inl ⋆ = H^-1 (H (inl ⋆)) : (to_left_inv H (inl ⋆))^-1
           ... = H^-1 (inl u') : {Hu'}
           ... = H^-1 (inl u) : is_prop.elim
           ... = H^-1 (H (inr a)) : {Hu^-1}
           ... = inr a : to_left_inv H (inr a)
Defined.

Definition unit_sum_equiv_cancel_inv (b : B) :
    unit_sum_equiv_cancel_map H (unit_sum_equiv_cancel_map H^-1ᵉ b) = b.
Proof.
    esimp[unit_sum_equiv_cancel_map], apply sum.rec,
    { intro x, cases x with u Hu, esimp, apply sum.rec,
      { intro x, exfalso, cases x with u' Hu', apply empty_of_inl_eq_inr,
        calc inl ⋆ = H^-1 (H (inl ⋆)) : (to_left_inv H (inl ⋆))^-1
               ... = H^-1 (inl u')    : ap H^-1 Hu'
               ... = H^-1 (inl u)     : {!is_prop.elim}
               ... = H^-1 (H (inr _)) : {Hu^-1}
               ... = inr _ : to_left_inv H },
      { intro x, cases x with b' Hb', esimp, cases sum.mem_cases (H^-1 (inr b)) with x x,
        { cases x with u' Hu', cases u', apply eq_of_inr_eq_inr,
          calc inr b' = H (inl ⋆)       : Hb'^-1
                  ... = H (H^-1 (inr b)) : (ap H Hu')^-1
                  ... = inr b           : to_right_inv H (inr b)},
        { exfalso, cases x with a Ha, apply empty_of_inl_eq_inr,
          cases u, apply concat, apply Hu^-1, apply concat, rotate 1, apply !(to_right_inv H),
          apply ap H,
          apply concat, rotate 1, apply Ha^-1, apply ap inr, esimp,
          apply sum.rec, intro x, exfalso, apply empty_of_inl_eq_inr,
          apply concat, exact x.2^-1, apply Ha,
          intro x, cases x with a' Ha', esimp, apply eq_of_inr_eq_inr, apply Ha'^-1 @ Ha } } },
    { intro x, cases x with b' Hb', esimp, apply eq_of_inr_eq_inr, refine Hb'^-1 @ _,
      cases sum.mem_cases (H^-1 (inr b)) with x x,
      { cases x with u Hu, esimp, cases sum.mem_cases (H^-1 (inl ⋆)) with x x,
        { cases x with u' Hu', exfalso, apply empty_of_inl_eq_inr,
          calc inl ⋆ = H (H^-1 (inl ⋆))  : (to_right_inv H (inl ⋆))^-1
                 ... = H (inl u')       : ap H Hu'
                 ... = H (inl u)        : by rewrite [is_prop.elim u' u]
                 ... = H (H^-1 (inr b))  : ap H Hu^-1
                 ... = inr b            : to_right_inv H (inr b) },
      { cases x with a Ha, exfalso, apply empty_of_inl_eq_inr,
        apply concat, rotate 1, exact Hb',
        have Ha' : inl ⋆ = H (inr a), by apply !(to_right_inv H)^-1 @ ap H Ha,
        apply concat Ha', apply ap H, apply ap inr, apply sum.rec,
          intro x, cases x with u' Hu', esimp, apply sum.rec,
            intro x, cases x with u'' Hu'', esimp, apply empty.rec,
            intro x, cases x with a'' Ha'', esimp, krewrite Ha' at Ha'', apply eq_of_inr_eq_inr,
            apply !(to_left_inv H)^-1 @ Ha'',
          intro x, exfalso, cases x with a'' Ha'', apply empty_of_inl_eq_inr,
          apply Hu^-1 @ Ha'', } },
      { cases x with a' Ha', esimp, refine _ @ !(to_right_inv H), apply ap H,
        apply Ha'^-1 } }
Defined.

Definition unit_sum_equiv_cancel : A <~> B.
Proof.
    fapply equiv.MK, apply unit_sum_equiv_cancel_map H,
    apply unit_sum_equiv_cancel_map H^-1ᵉ,
    intro b, apply unit_sum_equiv_cancel_inv,
    { intro a, have H = (H^-1ᵉ)^-1ᵉ, from !equiv.symm_symm^-1, rewrite this at {2},
      apply unit_sum_equiv_cancel_inv }
Defined.

Defined.

  (* universal property *)

Definition sum_rec_unc {P : A + B -> Type} (fg : (forall a, P (inl a)) \* (forall b, P (inr b)))
    : forall z, P z.
  sum.rec fg.1 fg.2

Definition is_equiv_sum_rec (P : A + B -> Type)
    : is_equiv (sum_rec_unc : (forall a, P (inl a)) \* (forall b, P (inr b)) -> forall z, P z).
Proof.
     apply adjointify sum_rec_unc (fun f => (fun a => f (inl a), fun b => f (inr b))),
       intro f, apply eq_of_homotopy, intro z, focus (induction z; all_goals reflexivity),
       intro h, induction h with f g, reflexivity
Defined.

Definition equiv_sum_rec (P : A + B -> Type)
    : (forall a, P (inl a)) \* (forall b, P (inr b)) <~> forall z, P z.
  equiv.mk _ !is_equiv_sum_rec

Definition imp_prod_imp_equiv_sum_imp (A B C : Type)
    : (A -> C) \* (B -> C) <~> (A + B -> C).
  !equiv_sum_rec

  (* truncatedness *)

  variables (A B)
Definition is_trunc_sum (n : trunc_index) [HA : is_trunc (n.+2) A]  [HB : is_trunc (n.+2) B]
    : is_trunc (n.+2) (A + B).
Proof.
    apply is_trunc_succ_intro, intro z z',
    apply is_trunc_equiv_closed_rev, apply sum_eq_equiv,
    induction z with a b, all_goals induction z' with a' b', all_goals esimp,
    all_goals exact _,
Defined.

Definition is_trunc_sum_excluded (n : trunc_index) [HA : is_trunc n A]  [HB : is_trunc n B]
    (H : A -> B -> empty) : is_trunc n (A + B).
Proof.
    induction n with n IH,
    { exfalso, exact H !center !center},
    { clear IH, induction n with n IH,
      { apply is_prop.mk, intros x y,
        induction x, all_goals induction y, all_goals esimp,
        all_goals try (exfalso;apply H;assumption;assumption), all_goals apply ap _ !is_prop.elim},
      { apply is_trunc_sum}}
Defined.

  variable {B}
Definition is_contr_sum_left [HA : is_contr A] (H : ¬B) : is_contr (A + B).
  is_contr.mk (inl !center)
              (fun x => sum.rec_on x (fun a => ap inl !center_eq) (fun b => empty.elim (H b)))

  (*
    Sums are equivalent to dependent sigmas where the first component is a bool.

    The current construction only works for A and B in the same universe.
    If we need it for A and B in different universes, we need to insert some lifts.
  *)

Definition sum_of_sigma_bool {A B : Type.{u}} (v : Σ(b : bool), bool.rec A B b) : A + B.
  by induction v with b x; induction b; exact inl x; exact inr x

Definition sigma_bool_of_sum {A B : Type.{u}} (z : A + B) : Σ(b : bool), bool.rec A B b.
  by induction z with a b; exact ⟨ff, a⟩; exact ⟨tt, b⟩

Definition sum_equiv_sigma_bool (A B : Type.{u})
    : A + B <~> Σ(b : bool), bool.rec A B b.
  equiv.MK sigma_bool_of_sum
           sum_of_sigma_bool
           begin intro v, induction v with b x, induction b, all_goals reflexivity end
           begin intro z, induction z with a b, all_goals reflexivity end

  (* pointed sums. We arbitrarily choose (inl (point _)) as basepoint for the sum *)

  open pointed
Definition psum (A B : pType) : pType.
  pointed.MK (A ⊎ B) (inl (point _))

  infixr ` +* `:30 . psum


Defined. sum
open sum pi

namespace decidable

Definition decidable_equiv (A : Type) : decidable A <~> A + ¬A.
Proof.
    fapply equiv.MK:intro a;induction a:try (constructor;assumption;now),
    all_goals reflexivity
Defined.

Definition is_trunc_decidable (A : Type) (n : trunc_index) [H : is_trunc n A] :
    is_trunc n (decidable A).
Proof.
    apply is_trunc_equiv_closed_rev,
    apply decidable_equiv,
    induction n with n IH,
    { apply is_contr_sum_left, exact fun na => na !center},
    { apply is_trunc_sum_excluded, exact fun a na => na a}
Defined.

Defined. decidable



Definition tsum {n : trunc_index} (A B : (n.+2)-Type) : (n.+2)-Type.
trunctype.mk (A + B) _

infixr `+t`:25 . tsum
