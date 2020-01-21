(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Floris van Doorn

Partially ported from the standard library
*)

open eq eq.ops decidable

namespace bool
  local attribute bor [reducible]
  local attribute band [reducible]

Definition dichotomy (b : bool) : b = ff ⊎ b = tt.
  bool.cases_on b (sum.inl rfl) (sum.inr rfl)

Definition cond_ff {A : Type} (t e : A) : cond ff t e = e.
  rfl

Definition cond_tt {A : Type} (t e : A) : cond tt t e = t.
  rfl

Definition eq_tt_of_ne_ff : forall {a : bool}, a ≠ ff -> a = tt
  | @eq_tt_of_ne_ff tt H . rfl
  | @eq_tt_of_ne_ff ff H . absurd rfl H

Definition eq_ff_of_ne_tt : forall {a : bool}, a ≠ tt -> a = ff
  | @eq_ff_of_ne_tt tt H . absurd rfl H
  | @eq_ff_of_ne_tt ff H . rfl

Definition absurd_of_eq_ff_of_eq_tt {B : Type} {a : bool} (H₁ : a = ff) (H₂ : a = tt) : B.
  absurd (H₁^-1 @ H₂) ff_ne_tt

Definition tt_bor (a : bool) : bor tt a = tt.
  rfl

  notation a || b . bor a b

Definition bor_tt (a : bool) : a || tt = tt.
  bool.cases_on a rfl rfl

Definition ff_bor (a : bool) : ff || a = a.
  bool.cases_on a rfl rfl

Definition bor_ff (a : bool) : a || ff = a.
  bool.cases_on a rfl rfl

Definition bor_self (a : bool) : a || a = a.
  bool.cases_on a rfl rfl

Definition bor.comm (a b : bool) : a || b = b || a.
  by cases a; repeat (cases b | reflexivity)

Definition bor.assoc (a b c : bool) : (a || b) || c = a || (b || c).
  match a with
  | ff . by rewrite *ff_bor
  | tt . by rewrite *tt_bor
Defined.

Definition or_of_bor_eq {a b : bool} : a || b = tt -> a = tt ⊎ b = tt.
  bool.rec_on a
    (suppose ff || b = tt,
      have b = tt, from !ff_bor # this,
      sum.inr this)
    (suppose tt || b = tt,
      sum.inl rfl)

Definition bor_inl {a b : bool} (H : a = tt) : a || b = tt.
  by rewrite H

Definition bor_inr {a b : bool} (H : b = tt) : a || b = tt.
  bool.rec_on a (by rewrite H) (by rewrite H)

Definition ff_band (a : bool) : ff && a = ff.
  rfl

Definition tt_band (a : bool) : tt && a = a.
  bool.cases_on a rfl rfl

Definition band_ff (a : bool) : a && ff = ff.
  bool.cases_on a rfl rfl

Definition band_tt (a : bool) : a && tt = a.
  bool.cases_on a rfl rfl

Definition band_self (a : bool) : a && a = a.
  bool.cases_on a rfl rfl

Definition band.comm (a b : bool) : a && b = b && a.
  bool.cases_on a
    (bool.cases_on b rfl rfl)
    (bool.cases_on b rfl rfl)

Definition band.assoc (a b c : bool) : (a && b) && c = a && (b && c).
  match a with
  | ff . by rewrite *ff_band
  | tt . by rewrite *tt_band
Defined.

Definition band_elim_left {a b : bool} (H : a && b = tt) : a = tt.
  sum.elim (dichotomy a)
    (suppose a = ff,
      absurd
        (calc ff = ff && b : ff_band
             ... = a && b  : this
             ... = tt      : H)
        ff_ne_tt)
    (suppose a = tt, this)

Definition band_intro {a b : bool} (H₁ : a = tt) (H₂ : b = tt) : a && b = tt.
  by rewrite [H₁, H₂]

Definition band_elim_right {a b : bool} (H : a && b = tt) : b = tt.
  band_elim_left (!band.comm @ H)

Definition bnot_bnot (a : bool) : bnot (bnot a) = a.
  bool.cases_on a rfl rfl

Definition bnot_empty : bnot ff = tt.
  rfl

Definition bnot_unit  : bnot tt = ff.
  rfl

Definition eq_tt_of_bnot_eq_ff {a : bool} : bnot a = ff -> a = tt.
  bool.cases_on a (by contradiction) (fun h => rfl)

Definition eq_ff_of_bnot_eq_tt {a : bool} : bnot a = tt -> a = ff.
  bool.cases_on a (fun h => rfl) (by contradiction)

Definition bxor (x:bool) (y:bool) . cond x (bnot y) y

  (* HoTT-related stuff *)
  open is_equiv equiv function is_trunc option unit decidable


Definition is_equiv_bnot [instance] [priority 500] : is_equiv bnot.
Proof.
    fapply is_equiv.mk,
      exact bnot,
      all_goals (intro b;cases b), do 6 reflexivity
  (*    all_goals (focus (intro b;cases b;all_goals reflexivity)), *)
Defined.

Definition bnot_ne : forall (b : bool), bnot b ≠ b
  | bnot_ne tt . ff_ne_tt
  | bnot_ne ff . ne.symm ff_ne_tt

Definition equiv_bnot : bool <~> bool . equiv.mk bnot _
Definition eq_bnot    : bool = bool . ua equiv_bnot

Definition eq_bnot_ne_idp : eq_bnot ≠ idp.
  assume H : eq_bnot = idp,
  have H2 : bnot = id, from !cast_ua_fn^-1 @ ap cast H,
  absurd (ap10 H2 tt) ff_ne_tt

Definition is_set_bool : is_set bool . _
Definition not_is_prop_bool_eq_bool : ¬ is_prop (bool = bool).
  fun H => eq_bnot_ne_idp !is_prop.elim

Definition bool_equiv_option_unit : bool <~> option unit.
Proof.
    fapply equiv.MK,
    { intro b, cases b, exact none, exact some star},
    { intro u, cases u, exact ff, exact tt},
    { intro u, cases u with u, reflexivity, cases u, reflexivity},
    { intro b, cases b, reflexivity, reflexivity},
Defined.

  (* pointed and truncated bool *)
  open pointed
Definition pointed_bool [instance] : pointed bool.
  pointed.mk ff

Definition pbool : Set*.
  pSet.mk' bool

Definition tbool : Set . trunctype.mk bool _

  notation `bool*` . pbool


Defined. bool
