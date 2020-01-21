(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about the natural numbers specific to HoTT
*)

import .order types.pointed .sub

open is_trunc unit empty eq equiv algebra pointed is_equiv equiv function

namespace nat
Definition is_prop_le [instance] (n m : ℕ) : is_prop (n ≤ m) :=
Proof.
    have lem : forall {n m : ℕ} (p : n ≤ m) (q : n = m), p = q # le.refl n,
    begin
      intros, cases p,
      { have H' : q = idp, by apply is_set.elim,
        cases H', reflexivity},
      { cases q, exfalso, apply not_succ_le_self a}
    end,
    apply is_prop.mk, intro H1 H2, induction H2,
    { apply lem},
    { cases H1,
      { exfalso, apply not_succ_le_self a},
      { exact ap le.step !v_0}},
Defined.

Definition is_prop_lt [instance] (n m : ℕ) : is_prop (n < m) := !is_prop_le

Definition le_equiv_succ_le_succ (n m : ℕ) : (n ≤ m) <~> (succ n ≤ succ m) :=
  equiv_of_is_prop succ_le_succ le_of_succ_le_succ
Definition le_succ_equiv_pred_le (n m : ℕ) : (n ≤ succ m) <~> (pred n ≤ m) :=
  equiv_of_is_prop pred_le_pred le_succ_of_pred_le

Definition lt_by_cases_lt {a b : ℕ} {P : Type} (H1 : a < b -> P) (H2 : a = b -> P)
    (H3 : a > b -> P) (H : a < b) : lt.by_cases H1 H2 H3 = H1 H :=
Proof.
    unfold lt.by_cases, induction (lt.trichotomy a b) with H' H',
     { esimp, exact ap H1 !is_prop.elim},
     { exfalso, cases H' with H' H', apply lt.irrefl, exact H' # H, exact lt.asymm H H'}
Defined.

Definition lt_by_cases_eq {a b : ℕ} {P : Type} (H1 : a < b -> P) (H2 : a = b -> P)
    (H3 : a > b -> P) (H : a = b) : lt.by_cases H1 H2 H3 = H2 H :=
Proof.
    unfold lt.by_cases, induction (lt.trichotomy a b) with H' H',
    { exfalso, apply lt.irrefl, exact H # H'},
    { cases H' with H' H', esimp, exact ap H2 !is_prop.elim, exfalso, apply lt.irrefl, exact H # H'}
Defined.

Definition lt_by_cases_ge {a b : ℕ} {P : Type} (H1 : a < b -> P) (H2 : a = b -> P)
    (H3 : a > b -> P) (H : a > b) : lt.by_cases H1 H2 H3 = H3 H :=
Proof.
    unfold lt.by_cases, induction (lt.trichotomy a b) with H' H',
    { exfalso, exact lt.asymm H H'},
    { cases H' with H' H', exfalso, apply lt.irrefl, exact H' # H, esimp, exact ap H3 !is_prop.elim}
Defined.

Definition lt_ge_by_cases_lt {n m : ℕ} {P : Type} (H1 : n < m -> P) (H2 : n ≥ m -> P)
    (H : n < m) : lt_ge_by_cases H1 H2 = H1 H :=
  by apply lt_by_cases_lt

Definition lt_ge_by_cases_ge {n m : ℕ} {P : Type} (H1 : n < m -> P) (H2 : n ≥ m -> P)
    (H : n ≥ m) : lt_ge_by_cases H1 H2 = H2 H :=
Proof.
    unfold [lt_ge_by_cases,lt.by_cases], induction (lt.trichotomy n m) with H' H',
    { exfalso, apply lt.irrefl, exact lt_of_le_of_lt H H'},
    { cases H' with H' H'; all_goals (esimp; apply ap H2 !is_prop.elim)}
Defined.

Definition lt_ge_by_cases_le {n m : ℕ} {P : Type} {H1 : n ≤ m -> P} {H2 : n ≥ m -> P}
    (H : n ≤ m) (Heq : forall (p : n = m), H1 (le_of_eq p) = H2 (le_of_eq p^-1))
    : lt_ge_by_cases (fun H' => H1 (le_of_lt H')) H2 = H1 H :=
Proof.
    unfold [lt_ge_by_cases,lt.by_cases], induction (lt.trichotomy n m) with H' H',
    { esimp, apply ap H1 !is_prop.elim},
    { cases H' with H' H',
      { esimp, induction H', esimp, symmetry,
        exact ap H1 !is_prop.elim @ Heq idp @ ap H2 !is_prop.elim},
      { exfalso, apply lt.irrefl, apply lt_of_le_of_lt H H'}}
Defined.

  protectedDefinition code [unfold 1 2] : ℕ -> ℕ -> Type₀
  | code 0        0        := unit
  | code 0        (succ m) := empty
  | code (succ n) 0        := empty
  | code (succ n) (succ m) := code n m

  protectedDefinition refl : forall n, nat.code n n
  | refl 0        := star
  | refl (succ n) := refl n

  protectedDefinition encode {n m : ℕ} (p : n = m) : nat.code n m :=
  p # nat.refl n

  protectedDefinition decode : forall (n m : ℕ), nat.code n m -> n = m
  | decode 0        0        := fun c => idp
  | decode 0        (succ l) := fun c => empty.elim c _
  | decode (succ k) 0        := fun c => empty.elim c _
  | decode (succ k) (succ l) := fun c => ap succ (decode k l c)

Definition nat_eq_equiv (n m : ℕ) : (n = m) <~> nat.code n m :=
  equiv.MK nat.encode
           !nat.decode
           begin
             revert m, induction n, all_goals (intro m;induction m;all_goals intro c),
               all_goals try contradiction,
               induction c, reflexivity,
               xrewrite [↑nat.decode,-tr_compose,v_0],
           end
           begin
             intro p, induction p, esimp, induction n,
               reflexivity,
               rewrite [↑nat.decode,↑nat.refl,v_0]
           end

Definition pointed_nat [instance] : pointed ℕ :=
  pointed.mk 0

  open sigma sum
Definition eq_even_or_eq_odd (n : ℕ) : (Σk, 2 * k = n) ⊎ (Σk, 2 * k + 1 = n) :=
Proof.
    induction n with n IH,
    { exact inl ⟨0, idp⟩},
    { induction IH with H H: induction H with k p: induction p,
      { exact inr ⟨k, idp⟩},
      { refine inl ⟨k+1, idp⟩}}
Defined.

Definition rec_on_even_odd {P : ℕ -> Type} (n : ℕ) (H : forall k, P (2 * k)) (H2 : forall k, P (2 * k + 1))
    : P n :=
Proof.
    cases eq_even_or_eq_odd n with v v: induction v with k p: induction p,
    { exact H k},
    { exact H2 k}
Defined.

  (* this inequality comes up a couple of times when using the freudenthal suspensionDefinition *)
Definition add_mul_le_mul_add (n m k : ℕ) : n + (succ m) * k ≤ (succ m) * (n + k) :=
  calc
    n + (succ m) * k ≤ (m * n + n) + (succ m) * k : add_le_add_right !le_add_left _
      ... = (succ m) * n + (succ m) * k : by rewrite -succ_mul
      ... = (succ m) * (n + k) : !left_distrib^-1

  (*
    Some operations work only for successors. For example fin (succ n) has a 0 and a 1, but fin 0
    doesn't. However, we want a bit more, because sometimes we want a zero of (fin a)
    where a is either
    - equal to a successor, but notDefinitionally a successor (e.g. (0 : fin (3 + n)))
    -Definitionally equal to a successor, but not in a way that type class inference can infer.
      (e.g. (0 : fin 4). Note that 4 is bit0 (bit0 one), but (bit0 x) (defined as x + x),
        is not always a successor)
    To solve this we use an auxillary class `is_succ` which can solve whether a number is a
    successor.
  *)

  inductive is_succ [class] : ℕ -> Type :=
  | mk : forall (n : ℕ), is_succ (succ n)

  attribute is_succ.mk [instance]

Definition is_succ_1 [instance] : is_succ 1 := is_succ.mk 0

Definition is_succ_add_right [instance] (n m : ℕ) [H : is_succ m] : is_succ (n+m) :=
  by induction H with m; constructor

Definition is_succ_add_left [instance] [priority 900] (n m : ℕ) [H : is_succ n] :
    is_succ (n+m) :=
  by induction H with n; cases m with m: constructor

Definition is_succ_bit0 (n : ℕ) [H : is_succ n] : is_succ (bit0 n) :=
  by exact _

  (* level 2 is useful for abelian homotopy groups, which only exist at level 2 and higher *)
  inductive is_at_least_two [class] : ℕ -> Type :=
  | mk : forall (n : ℕ), is_at_least_two (succ (succ n))

  attribute is_at_least_two.mk [instance]

Definition is_at_least_two_add_right [instance] (n m : ℕ) [H : is_at_least_two m] :
    is_at_least_two (n+m) :=
  by induction H with m; constructor

Definition is_at_least_two_add_left [instance] (n m : ℕ) [H : is_at_least_two n] :
    is_at_least_two (n+m) :=
  by induction H with n; cases m with m: try cases m with m: constructor

Definition is_at_least_two_add_both [instance] [priority 900] (n m : ℕ)
    [H : is_succ n] [K : is_succ m] : is_at_least_two (n+m) :=
  by induction H with n; induction K with m; cases m with m: constructor

Definition is_at_least_two_bit0 (n : ℕ) [H : is_succ n] : is_at_least_two (bit0 n) :=
  by exact _

Definition is_at_least_two_bit1 (n : ℕ) [H : is_succ n] : is_at_least_two (bit1 n) :=
  by exact _

  (* some facts about iterate *)

Definition iterate_succ {A : Type} (f : A -> A) (n : ℕ) (x : A) :
    f^[succ n] x = f^[n] (f x) :=
  by induction n with n p; reflexivity; exact ap f p

  lemma iterate_sub {A : Type} (f : A <~> A) {n m : ℕ} (h : n ≥ m) (a : A) :
    iterate f (n - m) a = iterate f n (iterate f^-1 m a) :=
Proof.
    revert n h, induction m with m p: intro n h,
    { reflexivity },
    { cases n with n, exfalso, apply not_succ_le_zero _ h,
      rewrite [succ_sub_succ], refine p n (le_of_succ_le_succ h) @ _,
      refine ap (f^[n]) _ @ !iterate_succ^-1, exact !to_right_inv^-1 }
Defined.

Definition iterate_commute {A : Type} {f g : A -> A} (n : ℕ) (h : f o g == g o f) :
    iterate f n o g == g o iterate f n :=
  by induction n with n IH; reflexivity; exact fun x => ap f (IH x) @ !h

Definition iterate_equiv {A : Type} (f : A <~> A) (n : ℕ) : A <~> A :=
  equiv.mk (iterate f n)
           (by induction n with n IH; apply is_equiv_id; exact is_equiv_compose f (iterate f n))

Definition iterate_inv {A : Type} (f : A <~> A) (n : ℕ) :
    (iterate_equiv f n)^-1 == iterate f^-1 n :=
Proof.
    induction n with n p: intro a,
      reflexivity,
      exact p (f^-1 a) @ !iterate_succ^-1
Defined.

Definition iterate_left_inv {A : Type} (f : A <~> A) (n : ℕ) (a : A) : f^-1ᵉ^[n] (f^[n] a) = a :=
  (iterate_inv f n (f^[n] a))^-1 @ to_left_inv (iterate_equiv f n) a

Definition iterate_right_inv {A : Type} (f : A <~> A) (n : ℕ) (a : A) : f^[n] (f^-1ᵉ^[n] a) = a :=
  ap (f^[n]) (iterate_inv f n a)^-1 @ to_right_inv (iterate_equiv f n) a



Defined. nat
