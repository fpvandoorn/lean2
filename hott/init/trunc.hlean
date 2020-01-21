(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Floris van Doorn

Definition of is_trunc (n-truncatedness)

Ported from Coq HoTT.
*)

prelude
import .nat .logic .equiv .pathover
open eq nat sigma unit sigma.ops
--set_option class.force_new true

(* Truncation levels *)

inductive trunc_index : Type₀.
| minus_two : trunc_index
| succ : trunc_index -> trunc_index

open trunc_index

(*
   notation for trunc_index is -2, -1, 0, 1, ...
   from 0 and up this comes from the way numerals are parsed in Lean.
   Any structure with a 0, a 1, and a + have numerals defined in them.
*)

notation `ℕ₋₂` . trunc_index (* input using \N-2 *)

Definition has_zero_trunc_index [instance] [priority 2000] : has_zero ℕ₋₂.
has_zero.mk (succ (succ minus_two))

Definition has_one_trunc_index [instance] [priority 2000] : has_one ℕ₋₂.
has_one.mk (succ (succ (succ minus_two)))

namespace trunc_index

  notation `-1` . trunc_index.succ trunc_index.minus_two (* ISSUE: -1 gets printed as -2.+1? *)
  notation `-2` . trunc_index.minus_two
  postfix `.+1`:(max+1) . trunc_index.succ
  postfix `.+2`:(max+1) . fun n => (n .+1 .+1)

  --addition, where we add two to the result
Definition add_plus_two (n m : ℕ₋₂) : ℕ₋₂.
  trunc_index.rec_on m n (fun k l => l .+1)

  infix ` +2+ `:65 . trunc_index.add_plus_two

  (* addition of trunc_indices, where results smaller than -2 are changed to -2 *)
  protectedDefinition add (n m : ℕ₋₂) : ℕ₋₂.
  trunc_index.cases_on m
    (trunc_index.cases_on n -2 (fun n' => (trunc_index.cases_on n' -2 id)))
    (fun m' => trunc_index.cases_on m'
      (trunc_index.cases_on n -2 id)
      (add_plus_two n))

  (* we give a weird name to the reflexivity step to avoid overloading le.refl
     (which can be used if types.trunc is imported) *)
  inductive le (a : ℕ₋₂) : ℕ₋₂ -> Type.
  | tr_refl : le a a
  | step : forall {b}, le a b -> le a (b.+1)

Defined. trunc_index

Definition has_le_trunc_index [instance] [priority 2000] : has_le ℕ₋₂.
has_le.mk trunc_index.le



Definition has_add_trunc_index [instance] [priority 2000] : has_add ℕ₋₂.
has_add.mk trunc_index.add

namespace trunc_index

Definition sub_two (n : ℕ) : ℕ₋₂.
  nat.rec_on n -2 (fun n k => k.+1)

Definition add_two (n : ℕ₋₂) : ℕ.
  trunc_index.rec_on n nat.zero (fun n k => nat.succ k)

  postfix `.-2`:(max+1) . sub_two
  postfix `.-1`:(max+1) . fun n => (n .-2 .+1)

Definition of_nat [coercion] (n : ℕ) : ℕ₋₂.
  n.-2.+2

Definition succ_le_succ {n m : ℕ₋₂} (H : n ≤ m) : n.+1 ≤ m.+1.
  by induction H with m H IH; apply le.tr_refl; exact le.step IH

Definition minus_two_le (n : ℕ₋₂) : -2 ≤ n.
  by induction n with n IH; apply le.tr_refl; exact le.step IH

Defined. trunc_index open trunc_index

namespace is_trunc

  export [notation] [coercion] trunc_index

  (* truncated types *)

  (*
    Just as in Coq HoTT we define an internal version of contractibility and is_trunc, but we only
    use `is_trunc` and `is_contr`
  *)

  structure contr_internal (A : Type).
    (center : A)
    (center_eq : forall (a : A), center = a)

Definition is_trunc_internal (n : ℕ₋₂) : Type -> Type.
    trunc_index.rec_on n
      (fun A => contr_internal A)
      (fun n trunc_n A => (forall (x y : A), trunc_n (x = y)))

Defined. is_trunc open is_trunc

structure is_trunc [class] (n : ℕ₋₂) (A : Type).
  (to_internal : is_trunc_internal n A)

open nat num trunc_index

namespace is_trunc

  abbreviation is_contr . is_trunc -2
  abbreviation is_prop . is_trunc -1
  abbreviation is_set  . is_trunc 0

  variables {A B : Type}

Definition is_trunc_succ_intro (A : Type) (n : ℕ₋₂) [H : ∀x y : A, is_trunc n (x = y)]
    : is_trunc n.+1 A.
  is_trunc.mk (fun x y => !is_trunc.to_internal)

Definition is_trunc_eq [instance] [priority 1200]
    (n : ℕ₋₂) [H : is_trunc (n.+1) A] (x y : A) : is_trunc n (x = y).
  is_trunc.mk (is_trunc.to_internal (n.+1) A x y)

  (* contractibility *)

Definition is_contr.mk (center : A) (center_eq : forall (a : A), center = a) : is_contr A.
  is_trunc.mk (contr_internal.mk center center_eq)

Definition center (A : Type) [H : is_contr A] : A.
  contr_internal.center (is_trunc.to_internal -2 A)

Definition center' {A : Type} (H : is_contr A) : A . center A

Definition center_eq [H : is_contr A] (a : A) : !center = a.
  contr_internal.center_eq (is_trunc.to_internal -2 A) a

Definition eq_of_is_contr [H : is_contr A] (x y : A) : x = y.
  (center_eq x)^-1 @ (center_eq y)

Definition prop_eq_of_is_contr {A : Type} [H : is_contr A] {x y : A} (p q : x = y) : p = q.
  have K : ∀ (r : x = y), eq_of_is_contr x y = r, from (fun r => eq.rec_on r (con_Vp _)),
  (K p)^-1 @ K q

Definition is_contr_eq {A : Type} [H : is_contr A] (x y : A) : is_contr (x = y).
  is_contr.mk !eq_of_is_contr (fun p => !prop_eq_of_is_contr)
  local attribute is_contr_eq [instance]

  (* truncation is upward close *)

  (* n-types are also (n+1)-types *)
Definition is_trunc_succ [instance] [priority 900] (A : Type) (n : ℕ₋₂)
    [H : is_trunc n A] : is_trunc (n.+1) A.
  trunc_index.rec_on n
    (fun A (H : is_contr A) => !is_trunc_succ_intro)
    (fun n IH A (H : is_trunc (n.+1) A) => @is_trunc_succ_intro _ _ (fun x y => IH _ _))
    A H
  --in the proof the type of H is given explicitly to make it available for class inference

Definition is_trunc_of_le.{l} (A : Type.{l}) {n m : ℕ₋₂} (Hnm : n ≤ m)
    [Hn : is_trunc n A] : is_trunc m A.
Proof.
    induction Hnm with m Hnm IH,
    { exact Hn},
    { exact _}
Defined.

Definition is_trunc_of_imp_is_trunc {n : ℕ₋₂} (H : A -> is_trunc (n.+1) A)
    : is_trunc (n.+1) A.
  @is_trunc_succ_intro _ _ (fun x y => @is_trunc_eq _ _ (H x) x y)

Definition is_trunc_of_imp_is_trunc_of_le {n : ℕ₋₂} (Hn : -1 ≤ n) (H : A -> is_trunc n A)
    : is_trunc n A.
Proof.
    cases Hn with n' Hn': apply is_trunc_of_imp_is_trunc H
Defined.

  (* these must beDefinitions, because we need them to compute sometimes *)
Definition is_trunc_of_is_contr (A : Type) (n : ℕ₋₂) [H : is_contr A] : is_trunc n A.
  trunc_index.rec_on n H (fun n H => _)

Definition is_trunc_succ_of_is_prop (A : Type) (n : ℕ₋₂) [H : is_prop A]
      : is_trunc (n.+1) A.
  is_trunc_of_le A (show -1 ≤ n.+1, from succ_le_succ (minus_two_le n))

Definition is_trunc_succ_succ_of_is_set (A : Type) (n : ℕ₋₂) [H : is_set A]
      : is_trunc (n.+2) A.
  is_trunc_of_le A (show 0 ≤ n.+2, from succ_le_succ (succ_le_succ (minus_two_le n)))

  (* props *)

Definition is_prop.elim [H : is_prop A] (x y : A) : x = y.
  !center

Definition is_contr_of_inhabited_prop {A : Type} [H : is_prop A] (x : A) : is_contr A.
  is_contr.mk x (fun y => !is_prop.elim)

Definition is_prop_of_imp_is_contr {A : Type} (H : A -> is_contr A) : is_prop A.
  @is_trunc_succ_intro A -2
    (fun x y =>
      have H2 : is_contr A, from H x,
      !is_contr_eq)

Definition is_prop.mk {A : Type} (H : ∀x y : A, x = y) : is_prop A.
  is_prop_of_imp_is_contr (fun x => is_contr.mk x (H x))

Definition is_prop_elim_self {A : Type} {H : is_prop A} (x : A) : is_prop.elim x x = idp.
  !is_prop.elim

  (* sets *)

Definition is_set.mk (A : Type) (H : ∀(x y : A) (p q : x = y), p = q) : is_set A.
  @is_trunc_succ_intro _ _ (fun x y => is_prop.mk (H x y))

Definition is_set.elim [H : is_set A] (x y : A) (p q : x = y) : p = q.
  !is_prop.elim

  (* instances *)

Definition is_contr_sigma_eq [instance] [priority 800] {A : Type} (a : A)
    : is_contr (Σ(x : A), a = x).
  is_contr.mk (sigma.mk a idp) (fun p => sigma.rec_on p (fun b q => eq.rec_on q idp))

Definition is_contr_sigma_eq' [instance] [priority 800] {A : Type} (a : A)
    : is_contr (Σ(x : A), x = a).
  is_contr.mk (sigma.mk a idp) (fun p => sigma.rec_on p (fun b q => eq.rec_on q idp))

Definition ap_pr1_center_eq_sigma_eq {A : Type} {a x : A} (p : a = x)
    : ap pr₁ (center_eq ⟨x, p⟩) = p.
  by induction p; reflexivity

Definition ap_pr1_center_eq_sigma_eq' {A : Type} {a x : A} (p : x = a)
    : ap pr₁ (center_eq ⟨x, p⟩) = p^-1.
  by induction p; reflexivity

Definition is_contr_unit : is_contr unit.
  is_contr.mk star (fun p => unit.rec_on p idp)

Definition is_prop_empty : is_prop empty.
  is_prop.mk (fun x => !empty.elim x)

  local attribute is_contr_unit is_prop_empty [instance]

Definition is_trunc_unit [instance] (n : ℕ₋₂) : is_trunc n unit.
  !is_trunc_of_is_contr

Definition is_trunc_empty [instance] (n : ℕ₋₂) : is_trunc (n.+1) empty.
  !is_trunc_succ_of_is_prop

  (* interaction with equivalences *)

  section
  open is_equiv equiv

Definition is_contr_is_equiv_closed (f : A -> B) [Hf : is_equiv f] [HA: is_contr A]
    : (is_contr B).
  is_contr.mk (f (center A)) (fun p => eq_of_eq_inv !center_eq)

Definition is_contr_equiv_closed (H : A <~> B) [HA: is_contr A] : is_contr B.
  is_contr_is_equiv_closed (to_fun H)

Definition equiv_of_is_contr_of_is_contr [HA : is_contr A] [HB : is_contr B] : A <~> B.
  equiv.mk
    (fun a => center B)
    (is_equiv.adjointify (fun a => center B) (fun b => center A) center_eq center_eq)

Definition is_trunc_is_equiv_closed (n : ℕ₋₂) (f : A -> B) [H : is_equiv f]
    [HA : is_trunc n A] : is_trunc n B.
Proof.
    revert A HA B f H, induction n with n IH: intros,
    { exact is_contr_is_equiv_closed f},
    { apply is_trunc_succ_intro, intro x y,
      exact IH (f^-1 x = f^-1 y) _ (x = y) (ap f^-1)^-1 !is_equiv_inv}
Defined.

Definition is_trunc_is_equiv_closed_rev (n : ℕ₋₂) (f : A -> B) [H : is_equiv f]
    [HA : is_trunc n B] : is_trunc n A.
  is_trunc_is_equiv_closed n f^-1

Definition is_trunc_equiv_closed (n : ℕ₋₂) (f : A <~> B) [HA : is_trunc n A]
    : is_trunc n B.
  is_trunc_is_equiv_closed n (to_fun f)

Definition is_trunc_equiv_closed_rev (n : ℕ₋₂) (f : A <~> B) [HA : is_trunc n B]
    : is_trunc n A.
  is_trunc_is_equiv_closed n (to_inv f)

Definition is_equiv_of_is_prop [HA : is_prop A] [HB : is_prop B]
    (f : A -> B) (g : B -> A) : is_equiv f.
  is_equiv.mk f g (fun b => !is_prop.elim) (fun a => !is_prop.elim) (fun a => !is_set.elim)

Definition is_equiv_of_is_contr [HA : is_contr A] [HB : is_contr B]
    (f : A -> B) : is_equiv f.
  is_equiv.mk f (fun x => !center) (fun b => !is_prop.elim) (fun a => !is_prop.elim) (fun a => !is_set.elim)

Definition equiv_of_is_prop [HA : is_prop A] [HB : is_prop B]
    (f : A -> B) (g : B -> A) : A <~> B.
  equiv.mk f (is_equiv_of_is_prop f g)

Definition equiv_of_iff_of_is_prop [HA : is_prop A] [HB : is_prop B] (H : A ↔ B) : A <~> B.
  equiv_of_is_prop (iff.elim_left H) (iff.elim_right H)

  (* truncatedness of lift *)
Definition is_trunc_lift [instance] [priority 1450] (A : Type) (n : ℕ₋₂)
    [H : is_trunc n A] : is_trunc n (lift A).
  is_trunc_equiv_closed _ !equiv_lift

Defined.

  (* interaction with the Unit type *)

  open equiv
  (* A contractible type is equivalent to unit. *)
  variable (A)
Definition equiv_unit_of_is_contr [H : is_contr A] : A <~> unit.
  equiv.MK (fun (x : A) => ⋆)
           (fun (u : unit) => center A)
           (fun (u : unit) => unit.rec_on u idp)
           (fun (x : A) => center_eq x)

  (* interaction with pathovers *)
  variable {A}
  variables {C : A -> Type}
            {a a₂ : A} (p : a = a₂)
            (c : C a) (c₂ : C a₂)

Definition is_trunc_pathover [instance]
    (n : ℕ₋₂) [H : is_trunc (n.+1) (C a)] : is_trunc n (c =[p] c₂).
  is_trunc_equiv_closed_rev n !pathover_equiv_eq_tr

Definition is_prop.elimo [H : is_prop (C a)] : c =[p] c₂.
  pathover_of_eq_tr !is_prop.elim

Definition is_prop_elimo_self {A : Type} (B : A -> Type) {a : A} (b : B a) {H : is_prop (B a)} :
    @is_prop.elimo A B a a idp b b H = idpo.
  !is_prop.elim

  variables {p c c₂}
Definition is_set.elimo (q q' : c =[p] c₂) [H : is_set (C a)] : q = q'.
  !is_prop.elim

  (* TODO: port "Truncated morphisms" *)

  (* truncated universe *)

Defined. is_trunc

structure trunctype (n : ℕ₋₂).
  (carrier : Type)
  (struct : is_trunc n carrier)

notation n `-Type` . trunctype n
abbreviation Prop . -1-Type
abbreviation Set  . 0-Type




protected abbreviation Prop.mk . @trunctype.mk -1
protected abbreviation Set.mk . @trunctype.mk (-1.+1)

protectedDefinition trunctype.mk' (n : ℕ₋₂) (A : Type) [H : is_trunc n A]
  : n-Type.
trunctype.mk A H

namespace is_trunc

Definition tlift.{u v} {n : ℕ₋₂} (A : trunctype.{u} n)
    : trunctype.{max u v} n.
  trunctype.mk (lift A) !is_trunc_lift

Defined. is_trunc
