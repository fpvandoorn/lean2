(*
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Properties of trunc_index, is_trunc, trunctype, trunc, and the pointed versions of these
*)

(* NOTE: the fact that (is_trunc n A) is a mere proposition is proved in .prop_trunc *)

import .pointed ..function algebra.order types.nat.order types.unit

open eq sigma sigma.ops pi function equiv trunctype
     is_equiv prod pointed nat is_trunc algebra sum unit

  (* basic computation with ℕ₋₂, its operations and its order *)
namespace trunc_index

Definition minus_one_le_succ (n : ℕ₋₂) : -1 ≤ n.+1.
  succ_le_succ (minus_two_le n)

Definition zero_le_of_nat (n : ℕ) : 0 ≤ of_nat n.
  succ_le_succ !minus_one_le_succ

  open decidable
  protectedDefinition has_decidable_eq [instance] : forall (n m : ℕ₋₂), decidable (n = m)
  | has_decidable_eq -2     -2     . inl rfl
  | has_decidable_eq (n.+1) -2     . inr (by contradiction)
  | has_decidable_eq -2     (m.+1) . inr (by contradiction)
  | has_decidable_eq (n.+1) (m.+1).
      match has_decidable_eq n m with
      | inl xeqy . inl (by rewrite xeqy)
      | inr xney . inr (fun h : succ n = succ m => by injection h with xeqy; exact absurd xeqy xney)
      end

Definition not_succ_le_minus_two {n : ℕ₋₂} (H : n .+1 ≤ -2) : empty.
  by cases H

  protectedDefinition le_trans {n m k : ℕ₋₂} (H1 : n ≤ m) (H2 : m ≤ k) : n ≤ k.
Proof.
    induction H2 with k H2 IH,
    { exact H1},
    { exact le.step IH}
Defined.

Definition le_of_succ_le_succ {n m : ℕ₋₂} (H : n.+1 ≤ m.+1) : n ≤ m.
Proof.
    cases H with m H',
    { apply le.tr_refl},
    { exact trunc_index.le_trans (le.step !le.tr_refl) H'}
Defined.

Definition not_succ_le_self {n : ℕ₋₂} : ¬n.+1 ≤ n.
Proof.
    induction n with n IH: intro H,
    { exact not_succ_le_minus_two H},
    { exact IH (le_of_succ_le_succ H)}
Defined.

  protectedDefinition le_antisymm {n m : ℕ₋₂} (H1 : n ≤ m) (H2 : m ≤ n) : n = m.
Proof.
    induction H2 with n H2 IH,
    { reflexivity},
    { exfalso, apply @not_succ_le_self n, exact trunc_index.le_trans H1 H2}
Defined.

  protectedDefinition le_succ {n m : ℕ₋₂} (H1 : n ≤ m) : n ≤ m.+1.
  le.step H1

  protectedDefinition self_le_succ (n : ℕ₋₂) : n ≤ n.+1.
  le.step (trunc_index.le.tr_refl n)

  (* the order is total *)
  protectedDefinition le_sum_le (n m : ℕ₋₂) : n ≤ m ⊎ m ≤ n.
Proof.
    induction m with m IH,
    { exact inr !minus_two_le},
    { cases IH with H H,
      { exact inl (trunc_index.le_succ H)},
      { cases H with n' H,
        { exact inl !trunc_index.self_le_succ},
        { exact inr (succ_le_succ H)}}}
Defined.

Defined. trunc_index open trunc_index

Definition linear_weak_order_trunc_index [trans_instance] :
  linear_weak_order trunc_index.
linear_weak_order.mk le trunc_index.le.tr_refl @trunc_index.le_trans @trunc_index.le_antisymm
                     trunc_index.le_sum_le

namespace trunc_index

  (* moreDefinitions about truncation indices *)

Definition zero_add (n : ℕ₋₂) : (0 : ℕ₋₂) + n = n.
Proof.
    cases n with n, reflexivity,
    cases n with n, reflexivity,
    induction n with n IH, reflexivity, exact ap succ IH
Defined.

Definition add_zero (n : ℕ₋₂) : n + (0 : ℕ₋₂) = n.
  by reflexivity

Definition succ_add_nat (n : ℕ₋₂) (m : ℕ) : n.+1 + m = (n + m).+1.
  by induction m with m IH; reflexivity; exact ap succ IH

Definition nat_add_succ (n : ℕ) (m : ℕ₋₂) : n + m.+1 = (n + m).+1.
Proof.
    cases m with m, reflexivity,
    cases m with m, reflexivity,
    induction m with m IH, reflexivity, exact ap succ IH
Defined.

Definition add_nat_succ (n : ℕ₋₂) (m : ℕ) : n + (nat.succ m) = (n + m).+1.
  by reflexivity

Definition nat_succ_add (n : ℕ) (m : ℕ₋₂) : (nat.succ n) + m = (n + m).+1.
Proof.
    cases m with m, reflexivity,
    cases m with m, reflexivity,
    induction m with m IH, reflexivity, exact ap succ IH
Defined.

Definition sub_two_add_two (n : ℕ₋₂) : sub_two (add_two n) = n.
Proof.
    induction n with n IH,
    { reflexivity},
    { exact ap succ IH}
Defined.

Definition add_two_sub_two (n : ℕ) : add_two (sub_two n) = n.
Proof.
    induction n with n IH,
    { reflexivity},
    { exact ap nat.succ IH}
Defined.

Definition of_nat_add_plus_two_of_nat (n m : ℕ) : n +2+ m = of_nat (n + m + 2).
Proof.
    induction m with m IH,
    { reflexivity},
    { exact ap succ IH}
Defined.

Definition of_nat_add_of_nat (n m : ℕ) : of_nat n + of_nat m = of_nat (n + m).
Proof.
    induction m with m IH,
    { reflexivity},
    { exact ap succ IH}
Defined.

Definition succ_add_plus_two (n m : ℕ₋₂) : n.+1 +2+ m = (n +2+ m).+1.
Proof.
    induction m with m IH,
    { reflexivity},
    { exact ap succ IH}
Defined.

Definition add_plus_two_succ (n m : ℕ₋₂) : n +2+ m.+1 = (n +2+ m).+1.
  idp

Definition add_succ_succ (n m : ℕ₋₂) : n + m.+2 = n +2+ m.
  idp

Definition succ_add_succ (n m : ℕ₋₂) : n.+1 + m.+1 = n +2+ m.
Proof.
    cases m with m IH,
    { reflexivity},
    { apply succ_add_plus_two}
Defined.

Definition succ_succ_add (n m : ℕ₋₂) : n.+2 + m = n +2+ m.
Proof.
    cases m with m IH,
    { reflexivity},
    { exact !succ_add_succ @ !succ_add_plus_two}
Defined.

Definition succ_sub_two (n : ℕ) : (nat.succ n).-2 = n.-2 .+1 . rfl
Definition sub_two_succ_succ (n : ℕ) : n.-2.+1.+1 = n . rfl
Definition succ_sub_two_succ (n : ℕ) : (nat.succ n).-2.+1 = n . rfl

Definition of_nat_add_two (n : ℕ₋₂) : of_nat (add_two n) = n.+2.
Proof. induction n with n IH, reflexivity, exact ap succ IH end

Definition of_nat_le_of_nat {n m : ℕ} (H : n ≤ m) : (of_nat n ≤ of_nat m).
Proof.
    induction H with m H IH,
    { apply le.refl},
    { exact trunc_index.le_succ IH}
Defined.

Definition sub_two_le_sub_two {n m : ℕ} (H : n ≤ m) : n.-2 ≤ m.-2.
Proof.
    induction H with m H IH,
    { apply le.refl},
    { exact trunc_index.le_succ IH}
Defined.

Definition add_two_le_add_two {n m : ℕ₋₂} (H : n ≤ m) : add_two n ≤ add_two m.
Proof.
    induction H with m H IH,
    { reflexivity},
    { constructor, exact IH},
Defined.

Definition le_of_sub_two_le_sub_two {n m : ℕ} (H : n.-2 ≤ m.-2) : n ≤ m.
Proof.
    rewrite [-add_two_sub_two n, -add_two_sub_two m],
    exact add_two_le_add_two H,
Defined.

Definition le_of_of_nat_le_of_nat {n m : ℕ} (H : of_nat n ≤ of_nat m) : n ≤ m.
Proof.
    apply le_of_sub_two_le_sub_two,
    exact le_of_succ_le_succ (le_of_succ_le_succ H)
Defined.

  protectedDefinition succ_le_of_not_le {n m : ℕ₋₂} (H : ¬ n ≤ m) : m.+1 ≤ n.
Proof.
    cases (le.total n m) with H2 H2,
    { exfalso, exact H H2},
    { cases H2 with n' H2',
      { exfalso, exact H !le.refl},
      { exact succ_le_succ H2'}}
Defined.

Definition trunc_index.decidable_le [instance] : forall (n m : ℕ₋₂), decidable (n ≤ m).
Proof.
    intro n, induction n with n IH: intro m,
    { left, apply minus_two_le},
    cases m with m,
    { right, apply not_succ_le_minus_two},
    cases IH m with H H,
    { left, apply succ_le_succ H},
    right, intro H2, apply H, exact le_of_succ_le_succ H2
Defined.

Defined. trunc_index open trunc_index

namespace is_trunc

  variables {A B : Type} {n : ℕ₋₂}

  (* closure properties of truncatedness *)
Definition is_trunc_is_embedding_closed (f : A -> B) [Hf : is_embedding f] [HB : is_trunc n B]
    (Hn : -1 ≤ n) : is_trunc n A.
Proof.
    induction n with n,
      {exfalso, exact not_succ_le_minus_two Hn},
      {apply is_trunc_succ_intro, intro a a',
         fapply @is_trunc_is_equiv_closed_rev _ _ n (ap f)}
Defined.

Definition is_trunc_is_retraction_closed (f : A -> B) [Hf : is_retraction f]
    (n : ℕ₋₂) [HA : is_trunc n A] : is_trunc n B.
Proof.
    revert A B f Hf HA,
    induction n with n IH,
    { intro A B f Hf HA, induction Hf with g ε, fapply is_contr.mk,
      { exact f (center A)},
      { intro b, apply concat,
        { apply (ap f), exact (center_eq (g b))},
        { apply ε}}},
    { intro A B f Hf HA, induction Hf with g ε,
      apply is_trunc_succ_intro, intro b b',
      fapply (IH (g b = g b')),
      { intro q, exact ((ε b)^-1 @ ap f q @ ε b')},
      { apply (is_retraction.mk (ap g)),
        { intro p, induction p, {rewrite [↑ap, con.left_inv]}}},
      { apply is_trunc_eq}}
Defined.

Definition is_embedding_to_fun (A B : Type) : is_embedding (@to_fun A B) .
  fun f f' => !is_equiv_ap_to_fun

  (*Definitions about trunctype *)
  protectedDefinition trunctype.sigma_char.{l} (n : ℕ₋₂) :
    (trunctype.{l} n) <~> (Σ (A : Type.{l}), is_trunc n A).
Proof.
    fapply equiv.MK,
    { intro A, exact (⟨carrier A, struct A⟩)},
    { intro S, exact (trunctype.mk S.1 S.2)},
    { intro S, induction S with S1 S2, reflexivity},
    { intro A, induction A with A1 A2, reflexivity},
Defined.

Definition trunctype_eq_equiv (n : ℕ₋₂) (A B : n-Type) :
    (A = B) <~> (carrier A = carrier B).
  calc
    (A = B) <~> (to_fun (trunctype.sigma_char n) A = to_fun (trunctype.sigma_char n) B)
              : eq_equiv_fn_eq_of_equiv
      ... <~> ((to_fun (trunctype.sigma_char n) A).1 = (to_fun (trunctype.sigma_char n) B).1)
             : equiv.symm (!equiv_subtype)
      ... <~> (carrier A = carrier B) : equiv.refl

Definition is_trunc_trunctype [instance] (n : ℕ₋₂) : is_trunc n.+1 (n-Type).
Proof.
    apply is_trunc_succ_intro, intro X Y,
    fapply is_trunc_equiv_closed_rev, { apply trunctype_eq_equiv},
    fapply is_trunc_equiv_closed_rev, { apply eq_equiv_equiv},
    induction n,
    { apply @is_contr_of_inhabited_prop,
      { apply is_trunc_equiv },
      { apply equiv_of_is_contr_of_is_contr}},
    { apply is_trunc_equiv }
Defined.

  (* univalence for truncated types *)
Definition teq_equiv_equiv {n : ℕ₋₂} {A B : n-Type} : (A = B) <~> (A <~> B).
  trunctype_eq_equiv n A B @e eq_equiv_equiv A B

Definition tua {n : ℕ₋₂} {A B : n-Type} (f : A <~> B) : A = B.
  (trunctype_eq_equiv n A B)^-1ᶠ (ua f)

Definition tua_refl {n : ℕ₋₂} (A : n-Type) : tua (@erfl A) = idp.
Proof.
    refine ap (trunctype_eq_equiv n A A)^-1ᶠ (ua_refl A) @ _,
    refine ap (eq_of_fn_eq_fn _) _ @ !eq_of_fn_eq_fn'_idp ,
    apply ap (dpair_eq_dpair idp), apply is_prop.elim
Defined.

Definition tua_trans {n : ℕ₋₂} {A B C : n-Type} (f : A <~> B) (g : B <~> C)
    : tua (f @e g) = tua f @ tua g.
Proof.
    refine ap (trunctype_eq_equiv n A C)^-1ᶠ (ua_trans f g) @ _,
    refine ap (eq_of_fn_eq_fn _) _ @ !eq_of_fn_eq_fn'_con,
    refine _ @ !dpair_eq_dpair_con,
    apply ap (dpair_eq_dpair _), esimp, apply is_prop.elim
Defined.

Definition tua_symm {n : ℕ₋₂} {A B : n-Type} (f : A <~> B) : tua f^-1ᵉ = (tua f)^-1.
Proof.
    apply eq_inv_of_con_eq_idp',
    refine !tua_trans^-1 @ _,
    refine ap tua _ @ !tua_refl,
    apply equiv_eq, exact to_right_inv f
Defined.

Definition tcast {n : ℕ₋₂} {A B : n-Type} (p : A = B) (a : A) : B.
  cast (ap trunctype.carrier p) a

Definition ptcast {n : ℕ₋₂} {A B : n-pType} (p : A = B) : A ->* B.
  pcast (ap ptrunctype.to_pType p)

Definition tcast_tua_fn {n : ℕ₋₂} {A B : n-Type} (f : A <~> B) : tcast (tua f) = to_fun f.
Proof.
    cases A with A HA, cases B with B HB, esimp at *,
    induction f using rec_on_ua_idp, esimp,
    have HA = HB, from !is_prop.elim, cases this,
    exact ap tcast !tua_refl
Defined.

  (*Definitions about decidable equality and axiom K *)
Definition is_set_of_axiom_K {A : Type} (K : forall {a : A} (p : a = a), p = idp) : is_set A.
  is_set.mk _ (fun a b p q => eq.rec K q p)

Definition is_set_of_relation.{u} {A : Type.{u}} (R : A -> A -> Type.{u})
    (mere : forall (a b : A), is_prop (R a b)) (refl : forall (a : A), R a a)
    (imp : forall {a b : A}, R a b -> a = b) : is_set A.
  is_set_of_axiom_K
    (fun a p =>
      have H2 : transport (fun x => R a x -> a = x) p (@imp a a) = @imp a a, from !apdt,
      have H3 : forall (r : R a a), transport (fun x => a = x) p (imp r)
                              = imp (transport (fun x => R a x) p r), from
        to_fun (equiv.symm !heq_pi) H2 =>
      have H4 : imp (refl a) @ p = imp (refl a), from
        calc
          imp (refl a) @ p = transport (fun x => a = x) p (imp (refl a)) : eq_transport_r
            ... = imp (transport (fun x => R a x) p (refl a)) : H3
            ... = imp (refl a) : is_prop.elim,
      cancel_left (imp (refl a)) H4)

Definition relation_equiv_eq {A : Type} (R : A -> A -> Type)
    (mere : forall (a b : A), is_prop (R a b)) (refl : forall (a : A), R a a)
    (imp : forall {a b : A}, R a b -> a = b) (a b : A) : R a b <~> a = b.
  have is_set A, from is_set_of_relation R mere refl @imp,
  equiv_of_is_prop imp (fun p => p # refl a)

  local attribute not [reducible]
Definition is_set_of_double_neg_elim {A : Type} (H : forall (a b : A), ¬¬a = b -> a = b)
    : is_set A.
  is_set_of_relation (fun a b => ¬¬a = b) _ (fun a n => n idp) H

  section
  open decidable
  --this is proven differently in init.hedberg
Definition is_set_of_decidable_eq (A : Type) [H : decidable_eq A] : is_set A.
  is_set_of_double_neg_elim (fun a b => by_contradiction)
Defined.

Definition is_trunc_of_axiom_K_of_le {A : Type} {n : ℕ₋₂} (H : -1 ≤ n)
    (K : forall (a : A), is_trunc n (a = a)) : is_trunc (n.+1) A.
  @is_trunc_succ_intro _ _ (fun a b => is_trunc_of_imp_is_trunc_of_le H (fun p => eq.rec_on p !K))

Definition is_trunc_succ_of_is_trunc_loop (Hn : -1 ≤ n) (Hp : forall (a : A), is_trunc n (a = a))
    : is_trunc (n.+1) A.
Proof.
    apply is_trunc_succ_intro, intros a a',
    apply is_trunc_of_imp_is_trunc_of_le Hn, intro p,
    induction p, apply Hp
Defined.

Definition is_prop_iff_is_contr {A : Type} (a : A) :
    is_prop A ↔ is_contr A.
  iff.intro (fun H => is_contr.mk a (is_prop.elim a)) _

Definition is_trunc_succ_iff_is_trunc_loop (A : Type) (Hn : -1 ≤ n) :
    is_trunc (n.+1) A ↔ forall (a : A), is_trunc n (a = a).
  iff.intro _ (is_trunc_succ_of_is_trunc_loop Hn)

  (* use loopn in name *)
Definition is_trunc_iff_is_contr_loop_succ (n : ℕ) (A : Type)
    : is_trunc n A ↔ forall (a : A), is_contr (Ω[succ n](pointed.Mk a)).
Proof.
    revert A, induction n with n IH,
    { intro A, esimp [loopn], transitivity _,
      { apply is_trunc_succ_iff_is_trunc_loop, apply le.refl},
      { apply pi_iff_pi, intro a, esimp, apply is_prop_iff_is_contr, reflexivity}},
    { intro A, esimp [loopn],
      transitivity _,
      { apply @is_trunc_succ_iff_is_trunc_loop @n, esimp, apply minus_one_le_succ},
      apply pi_iff_pi, intro a, transitivity _, apply IH,
      transitivity _, apply pi_iff_pi, intro p,
      rewrite [loopn_space_loop_irrel n p], apply iff.refl, esimp,
      apply imp_iff, reflexivity}
Defined.

  (* use loopn in name *)
Definition is_trunc_iff_is_contr_loop (n : ℕ) (A : Type)
    : is_trunc (n.-2.+1) A ↔ (forall (a : A), is_contr (Ω[n](pointed.Mk a))).
Proof.
    induction n with n,
    { esimp [sub_two,loopn], apply iff.intro,
        intro H a, exact is_contr_of_inhabited_prop a,
        intro H, apply is_prop_of_imp_is_contr, exact H},
    { apply is_trunc_iff_is_contr_loop_succ},
Defined.

  (* rename to is_contr_loopn_of_is_trunc *)
Definition is_contr_loop_of_is_trunc (n : ℕ) (A : pType) [H : is_trunc (n.-2.+1) A] :
    is_contr (Ω[n] A).
Proof.
    induction A,
    apply iff.mp !is_trunc_iff_is_contr_loop H
Defined.

  (* rename to is_trunc_loopn_of_is_trunc *)
Definition is_trunc_loop_of_is_trunc (n : ℕ₋₂) (k : ℕ) (A : pType) [H : is_trunc n A] :
    is_trunc n (Ω[k] A).
Proof.
    induction k with k IH,
    { exact H},
    { apply is_trunc_eq}
Defined.

Definition is_trunc_loopn (k : ℕ₋₂) (n : ℕ) (A : pType) [H : is_trunc (k+n) A]
    : is_trunc k (Ω[n] A).
Proof.
    revert k H, induction n with n IH: intro k H, exact _,
    apply is_trunc_eq, apply IH, rewrite [succ_add_nat, add_nat_succ at H], exact H
Defined.

Definition is_set_loopn (n : ℕ) (A : pType) [is_trunc n A] : is_set (Ω[n] A).
  have is_trunc (0+[ℕ₋₂]n) A, by rewrite [trunc_index.zero_add]; exact _,
  is_trunc_loopn 0 n A

Definition pequiv_punit_of_is_contr (A : pType) (H : is_contr A) : A <~>* punit.
  pequiv_of_equiv (equiv_unit_of_is_contr A) (@is_prop.elim unit _ _ _)

Definition pequiv_punit_of_is_contr' (A : Type) (H : is_contr A)
    : pointed.MK A (center A) <~>* punit.
  pequiv_punit_of_is_contr (pointed.MK A (center A)) H

Definition is_trunc_is_contr_fiber (n : ℕ₋₂) {A B : Type} (f : A -> B)
    (b : B) [is_trunc n A] [is_trunc n B] : is_trunc n (is_contr (fiber f b)).
Proof.
    cases n,
    { apply is_contr_of_inhabited_prop, apply is_contr_fun_of_is_equiv =>
      apply is_equiv_of_is_contr },
    { apply is_trunc_succ_of_is_prop }
Defined.

Defined. is_trunc open is_trunc

namespace trunc
  universe variable u
  variables {n : ℕ₋₂} {A : Type.{u}} {B : Type} {a₁ a₂ a₃ a₄ : A}

Definition trunc_functor2 [unfold 6 7] {n : ℕ₋₂} {A B C : Type} (f : A -> B -> C)
    (x : trunc n A) (y : trunc n B) : trunc n C.
  by induction x with a; induction y with b; exact tr (f a b)

Definition tconcat [unfold 6 7] (p : trunc n (a₁ = a₂)) (q : trunc n (a₂ = a₃)) :
    trunc n (a₁ = a₃).
  trunc_functor2 concat p q

Definition tinverse (p : trunc n (a₁ = a₂)) : trunc n (a₂ = a₁).
  trunc_functor _ inverse p

Definition tidp : trunc n (a₁ = a₁).
  tr idp

Definition tassoc (p : trunc n (a₁ = a₂)) (q : trunc n (a₂ = a₃))
    (r : trunc n (a₃ = a₄)) : tconcat (tconcat p q) r = tconcat p (tconcat q r).
  by induction p; induction q; induction r; exact ap tr (concat_pp_p _ _ _)

Definition tidp_tcon (p : trunc n (a₁ = a₂)) : tconcat tidp p = p.
  by induction p; exact ap tr (concat_1p _)

Definition tcon_tidp (p : trunc n (a₁ = a₂)) : tconcat p tidp = p.
  by induction p; reflexivity

Definition left_tinv (p : trunc n (a₁ = a₂)) : tconcat (tinverse p) p = tidp.
  by induction p; exact ap tr (con_Vp _)

Definition right_tinv (p : trunc n (a₁ = a₂)) : tconcat p (tinverse p) = tidp.
  by induction p; exact ap tr (con_pV _)

Definition tap (f : A -> B) (p : trunc n (a₁ = a₂)) : trunc n (f a₁ = f a₂).
  trunc_functor _ (ap f) p

Definition tap_tidp (f : A -> B) : tap f (@tidp n A a₁) = tidp . idp
Definition tap_tcon (f : A -> B) (p : trunc n (a₁ = a₂)) (q : trunc n (a₂ = a₃)) :
    tap f (tconcat p q) = tconcat (tap f p) (tap f q).
  by induction p; induction q; exact ap tr (ap_pp _ _ _)

  (* characterization of equality in truncated types *)
  protectedDefinition code [unfold 3 4] (n : ℕ₋₂) (aa aa' : trunc n.+1 A) : trunctype.{u} n.
  by induction aa with a; induction aa' with a'; exact trunctype.mk' n (trunc n (a = a'))

  protectedDefinition encode [unfold 3 5] {n : ℕ₋₂} {aa aa' : trunc n.+1 A}
    : aa = aa' -> trunc.code n aa aa'.
Proof.
    intro p, induction p, induction aa with a, esimp, exact (tr idp)
Defined.

  protectedDefinition decode [unfold 3 4 5] {n : ℕ₋₂} (aa aa' : trunc n.+1 A) :
    trunc.code n aa aa' -> aa = aa'.
Proof.
    induction aa' with a', induction aa with a,
    esimp [trunc.code, trunc.rec_on], intro x,
    induction x with p, exact ap tr p,
Defined.

Definition trunc_eq_equiv (n : ℕ₋₂) (aa aa' : trunc n.+1 A)
    : aa = aa' <~> trunc.code n aa aa'.
Proof.
    fapply equiv.MK,
    { apply trunc.encode},
    { apply trunc.decode},
    { eapply (trunc.rec_on aa'), eapply (trunc.rec_on aa),
      intro a a' x, esimp [trunc.code, trunc.rec_on] at x,
      refine (@trunc.rec_on n _ _ x _ _),
        intro x, apply is_trunc_eq,
        intro p, induction p, reflexivity},
    { intro p, induction p, apply (trunc.rec_on aa), intro a, exact idp},
Defined.

Definition tr_eq_tr_equiv (n : ℕ₋₂) (a a' : A)
    : (tr a = tr a' :> trunc n.+1 A) <~> trunc n (a = a').
  !trunc_eq_equiv

Definition trunc_eq {n : ℕ₋₂} {a a' : A} (p : trunc n (a = a')) :tr a = tr a' :> trunc n.+1 A.
  !tr_eq_tr_equiv^-1ᵉ p

Definition code_mul {n : ℕ₋₂} {aa₁ aa₂ aa₃ : trunc n.+1 A}
    (g : trunc.code n aa₁ aa₂) (h : trunc.code n aa₂ aa₃) : trunc.code n aa₁ aa₃.
Proof.
    induction aa₁ with a₁, induction aa₂ with a₂, induction aa₃ with a₃,
    esimp at *, apply tconcat g h,
Defined.

  (* encode preserves concatenation *)
Definition encode_con' {n : ℕ₋₂} {aa₁ aa₂ aa₃ : trunc n.+1 A} (p : aa₁ = aa₂) (q : aa₂ = aa₃)
    : trunc.encode (p @ q) = code_mul (trunc.encode p) (trunc.encode q).
Proof.
    induction p, induction q, induction aa₁ with a₁, reflexivity
Defined.

Definition encode_con {n : ℕ₋₂} {a₁ a₂ a₃ : A} (p : tr a₁ = tr a₂ :> trunc (n.+1) A)
    (q : tr a₂ = tr a₃ :> trunc (n.+1) A)
    : trunc.encode (p @ q) = tconcat (trunc.encode p) (trunc.encode q).
  encode_con' p q

  (* the principle of unique choice *)
Definition unique_choice {P : A -> Type} [H : forall a, is_prop (P a)] (f : forall a, ∥ P a ∥) (a : A)
    : P a.
  !trunc_equiv (f a)

  (* transport over a truncated family *)
Definition trunc_transport {a a' : A} {P : A -> Type} (p : a = a') (n : ℕ₋₂) (x : P a)
    : transport (fun a => trunc n (P a)) p (tr x) = tr (p # x).
  by induction p; reflexivity

  (* pathover over a truncated family *)
Definition trunc_pathover {A : Type} {B : A -> Type} {n : ℕ₋₂} {a a' : A} {p : a = a'}
    {b : B a} {b' : B a'} (q : b =[p] b') : @tr n _ b =[p] @tr n _ b'.
  by induction q; constructor

  (* truncations preserve truncatedness *)
Definition is_trunc_trunc_of_is_trunc [instance] [priority 500] (A : Type)
    (n m : ℕ₋₂) [H : is_trunc n A] : is_trunc n (trunc m A).
Proof.
    revert A m H, eapply (trunc_index.rec_on n),
    { clear n, intro A m H, apply is_contr_equiv_closed,
      { apply equiv.symm, apply trunc_equiv, apply (@is_trunc_of_le _ -2), apply minus_two_le} },
    { clear n, intro n IH A m H, induction m with m,
      { apply (@is_trunc_of_le _ -2), apply minus_two_le},
      { apply is_trunc_succ_intro, intro aa aa',
        apply (@trunc.rec_on _ _ _ aa  (fun y => !is_trunc_succ_of_is_prop)),
        eapply (@trunc.rec_on _ _ _ aa' (fun y => !is_trunc_succ_of_is_prop)),
        intro a a', apply (is_trunc_equiv_closed_rev),
        { apply tr_eq_tr_equiv},
        { exact (IH _ _ _)}}}
Defined.

  (* equivalences between truncated types (see also hit.trunc) *)
Definition trunc_trunc_equiv_left (A : Type) {n m : ℕ₋₂} (H : n ≤ m)
    : trunc n (trunc m A) <~> trunc n A.
Proof.
    note H2 . is_trunc_of_le (trunc n A) H,
    fapply equiv.MK,
    { intro x, induction x with x, induction x with x, exact tr x},
    { intro x, induction x with x, exact tr (tr x)},
    { intro x, induction x with x, reflexivity},
    { intro x, induction x with x, induction x with x, reflexivity}
Defined.

Definition trunc_trunc_equiv_right (A : Type) {n m : ℕ₋₂} (H : n ≤ m)
    : trunc m (trunc n A) <~> trunc n A.
Proof.
    apply trunc_equiv,
    exact is_trunc_of_le _ H,
Defined.

Definition trunc_equiv_trunc_of_le {n m : ℕ₋₂} {A B : Type} (H : n ≤ m)
    (f : trunc m A <~> trunc m B) : trunc n A <~> trunc n B.
  (trunc_trunc_equiv_left A H)^-1ᵉ @e trunc_equiv_trunc n f @e trunc_trunc_equiv_left B H

Definition trunc_trunc_equiv_trunc_trunc (n m : ℕ₋₂) (A : Type)
    : trunc n (trunc m A) <~> trunc m (trunc n A).
Proof.
    fapply equiv.MK: intro x; induction x with x; induction x with x,
    { exact tr (tr x)},
    { exact tr (tr x)},
    { reflexivity},
    { reflexivity}
Defined.

Definition is_trunc_trunc_of_le (A : Type)
    (n : ℕ₋₂) {m k : ℕ₋₂} (H : m ≤ k) [is_trunc n (trunc k A)] : is_trunc n (trunc m A).
Proof.
    apply is_trunc_equiv_closed,
    { apply trunc_trunc_equiv_left, exact H},
Defined.

Definition trunc_functor_homotopy {X Y : Type} (n : ℕ₋₂) {f g : X -> Y}
    (p : f == g) (x : trunc n X) : trunc_functor n f x = trunc_functor n g x.
Proof.
    induction x with x, esimp, exact ap tr (p x)
Defined.

Definition trunc_functor_homotopy_of_le {n k : ℕ₋₂} {A B : Type} (f : A -> B) (H : n ≤ k) :
    to_fun (trunc_trunc_equiv_left B H) o
    trunc_functor n (trunc_functor k f) o
    to_fun (trunc_trunc_equiv_left A H)^-1ᵉ ~
      trunc_functor n f.
Proof.
    intro x, induction x with x, reflexivity
Defined.

Definition is_equiv_trunc_functor_of_le {n k : ℕ₋₂} {A B : Type} (f : A -> B) (H : n ≤ k)
    [is_equiv (trunc_functor k f)] : is_equiv (trunc_functor n f).
  is_equiv_of_equiv_of_homotopy (trunc_equiv_trunc_of_le H (equiv.mk (trunc_functor k f) _))
                                (trunc_functor_homotopy_of_le f H)

  (* trunc_functor preserves surjectivity *)

Definition is_surjective_trunc_functor {A B : Type} (n : ℕ₋₂) (f : A -> B) [H : is_surjective f]
    : is_surjective (trunc_functor n f).
Proof.
    cases n with n: intro b,
    { exact tr (fiber.mk !center !is_prop.elim)},
    { refine @trunc.rec _ _ _ _ _ b, {intro x, exact is_trunc_of_le _ !minus_one_le_succ},
      clear b, intro b, induction H b with a p,
      exact tr (fiber.mk (tr a) (ap tr p))}
Defined.

  (* truncation of pointed types *)
Definition ptrunc (n : ℕ₋₂) (X : pType) : n-pType.
  ptrunctype.mk (trunc n X) _ (tr (point _))

  (* pointed maps involving ptrunc *)
Definition ptrunc_functor {X Y : pType} (n : ℕ₋₂) (f : X ->* Y)
    : ptrunc n X ->* ptrunc n Y.
  Build_pMap (trunc_functor n f) (ap tr (point_eq f))

Definition ptr (n : ℕ₋₂) (A : pType) : A ->* ptrunc n A.
  Build_pMap tr idp

Definition puntrunc (n : ℕ₋₂) (A : pType) [is_trunc n A] : ptrunc n A ->* A.
  Build_pMap untrunc_of_is_trunc idp

Definition ptrunc.elim (n : ℕ₋₂) {X Y : pType} [is_trunc n Y] (f : X ->* Y) :
    ptrunc n X ->* Y.
  Build_pMap (trunc.elim f) (point_eq f)

  (* pointed equivalences involving ptrunc *)
Definition ptrunc_pequiv_ptrunc (n : ℕ₋₂) {X Y : pType} (H : X <~>* Y)
    : ptrunc n X <~>* ptrunc n Y.
  pequiv_of_equiv (trunc_equiv_trunc n H) (ap tr (point_eq H))

Definition ptrunc_pequiv (n : ℕ₋₂) (X : pType) [H : is_trunc n X]
    : ptrunc n X <~>* X.
  pequiv_of_equiv (trunc_equiv n X) idp

Definition ptrunc_ptrunc_pequiv_left (A : pType) {n m : ℕ₋₂} (H : n ≤ m)
    : ptrunc n (ptrunc m A) <~>* ptrunc n A.
  pequiv_of_equiv (trunc_trunc_equiv_left A H) idp

Definition ptrunc_ptrunc_pequiv_right (A : pType) {n m : ℕ₋₂} (H : n ≤ m)
    : ptrunc m (ptrunc n A) <~>* ptrunc n A.
  pequiv_of_equiv (trunc_trunc_equiv_right A H) idp

Definition ptrunc_pequiv_ptrunc_of_le {n m : ℕ₋₂} {A B : pType} (H : n ≤ m)
    (f : ptrunc m A <~>* ptrunc m B) : ptrunc n A <~>* ptrunc n B.
  (ptrunc_ptrunc_pequiv_left A H)^-1ᵉ* @e*
  ptrunc_pequiv_ptrunc n f @e*
  ptrunc_ptrunc_pequiv_left B H

Definition ptrunc_ptrunc_pequiv_ptrunc_ptrunc (n m : ℕ₋₂) (A : pType)
    : ptrunc n (ptrunc m A) <~>* ptrunc m (ptrunc n A).
  pequiv_of_equiv (trunc_trunc_equiv_trunc_trunc n m A) idp

Definition loop_ptrunc_pequiv (n : ℕ₋₂) (A : pType) :
    loops (ptrunc (n+1) A) <~>* ptrunc n (loops A).
  pequiv_of_equiv !tr_eq_tr_equiv idp

Definition loop_ptrunc_pequiv_con {n : ℕ₋₂} {A : pType} (p q : loops (ptrunc (n+1) A)) :
    loop_ptrunc_pequiv n A (p @ q) =
      tconcat (loop_ptrunc_pequiv n A p) (loop_ptrunc_pequiv n A q).
  encode_con p q

Definition loopn_ptrunc_pequiv (n : ℕ₋₂) (k : ℕ) (A : pType) :
    Ω[k] (ptrunc (n+k) A) <~>* ptrunc n (Ω[k] A).
Proof.
    revert n, induction k with k IH: intro n,
    { reflexivity},
    { refine _ @e* loop_ptrunc_pequiv n (Ω[k] A),
      change loops (Ω[k] (ptrunc (n + succ k) A)) <~>* loops (ptrunc (n + 1) (Ω[k] A)),
      apply loop_pequiv_loop,
      refine _ @e* IH (n.+1),
      exact loopn_pequiv_loopn k (pequiv_of_eq (ap (fun n => ptrunc n A) !succ_add_nat^-1)) }
Defined.

Definition loopn_ptrunc_pequiv_con {n : ℕ₋₂} {k : ℕ} {A : pType}
    (p q : Ω[succ k] (ptrunc (n+succ k) A)) :
    loopn_ptrunc_pequiv n (succ k) A (p @ q) =
    tconcat (loopn_ptrunc_pequiv n (succ k) A p)
            (loopn_ptrunc_pequiv n (succ k) A q) .
Proof.
    refine _ @ loop_ptrunc_pequiv_con _ _,
    exact ap !loop_ptrunc_pequiv !loop_pequiv_loop_con
Defined.

Definition loopn_ptrunc_pequiv_inv_con {n : ℕ₋₂} {k : ℕ} {A : pType}
    (p q : ptrunc n (Ω[succ k] A)) :
    (loopn_ptrunc_pequiv n (succ k) A)^-1ᵉ* (tconcat p q) =
    (loopn_ptrunc_pequiv n (succ k) A)^-1ᵉ* p @
    (loopn_ptrunc_pequiv n (succ k) A)^-1ᵉ* q.
  equiv.inv_preserve_binary (loopn_ptrunc_pequiv n (succ k) A) concat tconcat
    (@loopn_ptrunc_pequiv_con n k A) p q

  (* pointed homotopies involving ptrunc *)
Definition ptrunc_functor_pcompose {X Y Z : pType} (n : ℕ₋₂) (g : Y ->* Z)
    (f : X ->* Y) : ptrunc_functor n (g o* f) ==* ptrunc_functor n g o* ptrunc_functor n f.
Proof.
    fapply Build_pHomotopy,
    { apply trunc_functor_compose} =>
    { esimp, refine (concat_1p _) @ _, refine whisker_right _ !ap_compose'^-1ᵖ @ _,
      esimp, refine whisker_right _ (ap_compose' tr g _) @ _, exact (ap_pp _ _ _)^-1},
Defined.

Definition ptrunc_functor_pid (X : pType) (n : ℕ₋₂) :
    ptrunc_functor n (pid X) ==* pid (ptrunc n X).
Proof.
    fapply Build_pHomotopy,
    { apply trunc_functor_id} =>
    { reflexivity},
Defined.

Definition ptrunc_functor_pcast {X Y : pType} (n : ℕ₋₂) (p : X = Y) :
    ptrunc_functor n (pcast p) ==* pcast (ap (ptrunc n) p).
Proof.
    fapply Build_pHomotopy,
    { intro x, esimp, refine !trunc_functor_cast @ _ => refine ap010 cast _ x,
      refine !ap_compose'^-1 @ !ap_compose'},
    { induction p, reflexivity},
Defined.

Definition ptrunc_functor_phomotopy {X Y : pType} (n : ℕ₋₂) {f g : X ->* Y}
    (p : f ==* g) : ptrunc_functor n f ==* ptrunc_functor n g.
Proof.
    fapply Build_pHomotopy,
    { exact trunc_functor_homotopy n p} =>
    { esimp, refine (ap_pp _ _ _)^-1 @ _, exact ap02 tr !point_htpy},
Defined.

Definition pcast_ptrunc (n : ℕ₋₂) {A B : pType} (p : A = B) :
    pcast (ap (ptrunc n) p) ==* ptrunc_functor n (pcast p).
Proof.
    fapply Build_pHomotopy,
    { intro a, induction p, esimp, exact !trunc_functor_id^-1} =>
    { induction p, reflexivity}
Defined.

Definition ptrunc_elim_ptr (n : ℕ₋₂) {X Y : pType} [is_trunc n Y] (f : X ->* Y) :
    ptrunc.elim n f o* ptr n X ==* f.
Proof.
    fapply Build_pHomotopy,
    { reflexivity },
    { reflexivity }
Defined.

Definition ptrunc_elim_phomotopy (n : ℕ₋₂) {X Y : pType} [is_trunc n Y] {f g : X ->* Y}
    (H : f ==* g) : ptrunc.elim n f ==* ptrunc.elim n g.
Proof.
    fapply Build_pHomotopy,
    { intro x, induction x with x, exact H x },
    { exact point_htpy H }
Defined.

Definition ap1_ptrunc_functor (n : ℕ₋₂) {A B : pType} (f : A ->* B) :
    Ω-> (ptrunc_functor (n.+1) f) o* (loop_ptrunc_pequiv n A)^-1ᵉ* ==*
    (loop_ptrunc_pequiv n B)^-1ᵉ* o* ptrunc_functor n (Ω-> f).
Proof.
    fapply Build_pHomotopy,
    { intro p, induction p with p,
      refine (!ap_inv^-1 ◾ !ap_compose^-1 ◾ idp) @ _ @ (ap_pp _ _ _)^-1,
      apply whisker_right, refine _ @ (ap_pp _ _ _)^-1, exact whisker_left _ !ap_compose },
    { induction B with B b, induction f with f p, esimp at f, esimp at p, induction p, reflexivity }
Defined.

Definition ap1_ptrunc_elim (n : ℕ₋₂) {A B : pType} (f : A ->* B) [is_trunc (n.+1) B] :
    Ω-> (ptrunc.elim (n.+1) f) o* (loop_ptrunc_pequiv n A)^-1ᵉ* ==*
    ptrunc.elim n (Ω-> f).
Proof.
    fapply Build_pHomotopy,
    { intro p, induction p with p, exact idp ◾ !ap_compose^-1 ◾ idp },
    { reflexivity }
Defined.

Definition ap1_ptr (n : ℕ₋₂) (A : pType) :
    Ω-> (ptr (n.+1) A) ==* (loop_ptrunc_pequiv n A)^-1ᵉ* o* ptr n (loops A).
Proof.
    fapply Build_pHomotopy,
    { intro p, apply idp_con },
    { reflexivity }
Defined.

Definition ptrunc_elim_ptrunc_functor (n : ℕ₋₂) {A B C : pType} (g : B ->* C) (f : A ->* B)
    [is_trunc n C] :
    ptrunc.elim n g o* ptrunc_functor n f ==* ptrunc.elim n (g o* f).
Proof.
    fapply Build_pHomotopy,
    { intro x, induction x with a, reflexivity },
    { esimp, exact (concat_1p _) @ whisker_right _ !ap_compose },
Defined.

Defined. trunc open trunc

(* The truncated encode-decode method *)
namespace eq

Definition truncated_encode {k : ℕ₋₂} {A : Type} {a₀ a : A} {code : A -> Type}
    [forall a, is_trunc k (code a)] (c₀ : code a₀) (p : trunc k (a₀ = a)) : code a.
Proof.
    induction p with p,
    exact transport code p c₀
Defined.

Definition truncated_encode_decode_method {k : ℕ₋₂} {A : Type} (a₀ a : A) (code : A -> Type)
    [forall a, is_trunc k (code a)] (c₀ : code a₀)
    (decode : forall (a : A) (c : code a), trunc k (a₀ = a))
    (encode_decode : forall (a : A) (c : code a), truncated_encode c₀ (decode a c) = c)
    (decode_encode : decode a₀ c₀ = tr idp) : trunc k (a₀ = a) <~> code a.
Proof.
    fapply equiv.MK,
    { exact truncated_encode c₀},
    { apply decode},
    { intro c, apply encode_decode},
    { intro p, induction p with p, induction p, exact decode_encode},
Defined.

Defined. eq


(* some consequences for properties about functions (surjectivity etc.) *)
namespace function
  variables {A B : Type}
Definition is_surjective_of_is_equiv [instance] (f : A -> B) [H : is_equiv f] : is_surjective f.
  fun b => begin esimp, apply center, apply is_trunc_trunc_of_is_trunc end

Definition is_equiv_equiv_is_embedding_times_is_surjective (f : A -> B)
    : is_equiv f <~> (is_embedding f \* is_surjective f).
  equiv_of_is_prop (fun H => (_, _))
                    (fun P => prod.rec_on P (fun H₁ H₂ => !is_equiv_of_is_surjective_of_is_embedding))

  (*
    Theorem 8.8.1:
    A function is an equivalence if it's an embedding and it's action on sets is an surjection
  *)
Definition is_equiv_of_is_surjective_trunc_of_is_embedding {A B : Type} (f : A -> B)
    [H : is_embedding f] [H' : is_surjective (trunc_functor 0 f)] : is_equiv f.
  have is_surjective f,
Proof.
    intro b,
    induction H' (tr b) with a p,
    induction a with a, esimp at p,
    induction (tr_eq_tr_equiv _ _ _ p) with q,
    exact image.mk a q
Defined.,
  is_equiv_of_is_surjective_of_is_embedding f

  (*
    Corollary 8.8.2:
    A function f is an equivalence if Ωf and trunc_functor 0 f are equivalences
  *)
Definition is_equiv_of_is_equiv_ap1_of_is_equiv_trunc {A B : Type} (f : A -> B)
    [H : forall a, is_equiv (ap1 (pmap_of_map f a))] [H' : is_equiv (trunc_functor 0 f)] :
    is_equiv f.
  have is_embedding f,
Proof.
    intro a a',
    apply is_equiv_of_imp_is_equiv,
    intro p,
    note q . ap (@tr 0 _) p,
    note r . @(eq_of_fn_eq_fn' (trunc_functor 0 f)) _ (tr a) (tr a') q =>
    induction (tr_eq_tr_equiv _ _ _ r) with s,
    induction s,
    apply is_equiv.homotopy_closed (ap1 (pmap_of_map f a)),
    intro p, apply idp_con
Defined.,
  is_equiv_of_is_surjective_trunc_of_is_embedding f

  (* Whitehead's principle itself is in homotopy.homotopy_group, since it needs theDefinition of *)
  (* a homotopy group. *)

Defined. function
