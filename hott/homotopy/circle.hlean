(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the circle
*)

import .sphere
import types.int.hott
import algebra.homotopy_group .connectedness

open eq susp bool is_equiv equiv is_trunc is_conn pi algebra pointed

Definition circle : Type₀ . sphere 1

namespace circle
  notation `S¹` . circle
Definition base1 : S¹ . !north
Definition base2 : S¹ . !south
Definition seg1 : base1 = base2 . merid ff
Definition seg2 : base1 = base2 . merid tt

Definition base : S¹ . base1
Definition loop : base = base . seg2 @ seg1^-1

Definition rec2 {P : S¹ -> Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : Pb1 =[seg1] Pb2) (Ps2 : Pb1 =[seg2] Pb2) (x : S¹) : P x.
Proof.
    induction x with b,
    { exact Pb1 },
    { exact Pb2 },
    { esimp at *, induction b with y,
      { exact Ps1 },
      { exact Ps2 }},
Defined.

Definition rec2_on {P : S¹ -> Type} (x : S¹) (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : Pb1 =[seg1] Pb2) (Ps2 : Pb1 =[seg2] Pb2) : P x.
  circle.rec2 Pb1 Pb2 Ps1 Ps2 x

Definition rec2_seg1 {P : S¹ -> Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : Pb1 =[seg1] Pb2) (Ps2 : Pb1 =[seg2] Pb2)
      : apd (rec2 Pb1 Pb2 Ps1 Ps2) seg1 = Ps1.
  !rec_merid

Definition rec2_seg2 {P : S¹ -> Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : Pb1 =[seg1] Pb2) (Ps2 : Pb1 =[seg2] Pb2)
      : apd (rec2 Pb1 Pb2 Ps1 Ps2) seg2 = Ps2.
  !rec_merid

Definition elim2 {P : Type} (Pb1 Pb2 : P) (Ps1 Ps2 : Pb1 = Pb2) (x : S¹) : P.
  rec2 Pb1 Pb2 (pathover_of_eq _ Ps1) (pathover_of_eq _ Ps2) x

Definition elim2_on {P : Type} (x : S¹) (Pb1 Pb2 : P)
    (Ps1 : Pb1 = Pb2) (Ps2 : Pb1 = Pb2) : P.
  elim2 Pb1 Pb2 Ps1 Ps2 x

Definition elim2_seg1 {P : Type} (Pb1 Pb2 : P) (Ps1 : Pb1 = Pb2) (Ps2 : Pb1 = Pb2)
    : ap (elim2 Pb1 Pb2 Ps1 Ps2) seg1 = Ps1.
Proof.
    apply eq_of_fn_eq_fn_inv !(pathover_constant seg1),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim2,rec2_seg1],
Defined.

Definition elim2_seg2 {P : Type} (Pb1 Pb2 : P) (Ps1 : Pb1 = Pb2) (Ps2 : Pb1 = Pb2)
    : ap (elim2 Pb1 Pb2 Ps1 Ps2) seg2 = Ps2.
Proof.
    apply eq_of_fn_eq_fn_inv !(pathover_constant seg2),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim2,rec2_seg2],
Defined.

Definition elim2_type (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 <~> Pb2) (x : S¹) : Type.
  elim2 Pb1 Pb2 (ua Ps1) (ua Ps2) x

Definition elim2_type_on (x : S¹) (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 <~> Pb2)
    : Type.
  elim2_type Pb1 Pb2 Ps1 Ps2 x

Definition elim2_type_seg1 (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 <~> Pb2)
    : transport (elim2_type Pb1 Pb2 Ps1 Ps2) seg1 = Ps1.
  by rewrite [tr_eq_cast_ap_fn,↑elim2_type,elim2_seg1];apply cast_ua_fn

Definition elim2_type_seg2 (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 <~> Pb2)
    : transport (elim2_type Pb1 Pb2 Ps1 Ps2) seg2 = Ps2.
  by rewrite [tr_eq_cast_ap_fn,↑elim2_type,elim2_seg2];apply cast_ua_fn

  protectedDefinition rec {P : S¹ -> Type} (Pbase : P base) (Ploop : Pbase =[loop] Pbase)
    (x : S¹) : P x.
Proof.
    fapply (rec2_on x),
    { exact Pbase},
    { exact (transport P seg1 Pbase)},
    { apply pathover_tr},
    { apply pathover_tr_of_pathover, exact Ploop}
Defined.

  protectedDefinition rec_on {P : S¹ -> Type} (x : S¹) (Pbase : P base)
    (Ploop : Pbase =[loop] Pbase) : P x.
  circle.rec Pbase Ploop x

Definition rec_loop_helper {A : Type} (P : A -> Type)
    {x y z : A} {p : x = y} {p' : z = y} {u : P x} {v : P z} (q : u =[p @ p'^-1] v) :
    pathover_tr_of_pathover q @o !pathover_tr^-1ᵒ = q.
  by cases p'; cases q; exact idp

Definition con_refl {A : Type} {x y : A} (p : x = y) : p @ refl _ = p.
  eq.rec_on p idp

Definition rec_loop {P : S¹ -> Type} (Pbase : P base) (Ploop : Pbase =[loop] Pbase) :
    apd (circle.rec Pbase Ploop) loop = Ploop.
Proof.
    rewrite [↑loop,apd_con,↑circle.rec,↑circle.rec2_on,↑base,rec2_seg2,apd_inv,rec2_seg1],
    apply rec_loop_helper
Defined.

  protectedDefinition elim {P : Type} (Pbase : P) (Ploop : Pbase = Pbase)
    (x : S¹) : P.
  circle.rec Pbase (pathover_of_eq _ Ploop) x

  protectedDefinition elim_on {P : Type} (x : S¹) (Pbase : P)
    (Ploop : Pbase = Pbase) : P.
  circle.elim Pbase Ploop x

Definition elim_loop {P : Type} (Pbase : P) (Ploop : Pbase = Pbase) :
    ap (circle.elim Pbase Ploop) loop = Ploop.
Proof.
    apply eq_of_fn_eq_fn_inv !(pathover_constant loop),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑circle.elim,rec_loop],
Defined.

Definition elim_seg1 {P : Type} (Pbase : P) (Ploop : Pbase = Pbase)
    : ap (circle.elim Pbase Ploop) seg1 = (tr_constant seg1 Pbase)^-1.
Proof.
    apply eq_of_fn_eq_fn_inv !(pathover_constant seg1),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑circle.elim,↑circle.rec],
    rewrite [↑circle.rec2_on,rec2_seg1], apply inverse,
    apply pathover_of_eq_tr_constant_inv
Defined.

Definition elim_seg2 {P : Type} (Pbase : P) (Ploop : Pbase = Pbase)
    : ap (circle.elim Pbase Ploop) seg2 = Ploop @ (tr_constant seg1 Pbase)^-1.
Proof.
    apply eq_of_fn_eq_fn_inv !(pathover_constant seg2),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑circle.elim,↑circle.rec],
    rewrite [↑circle.rec2_on,rec2_seg2],
    assert l : forall (A B : Type)(a a₂ a₂' : A)(b b' : B)(p : a = a₂)(p' : a₂' = a₂)
                   (q : b = b'),
             pathover_tr_of_pathover (pathover_of_eq _ q)
           = pathover_of_eq _ (q @ (tr_constant p' b')^-1)
           :> b =[p] p' # b',
    { intros, cases q, cases p', cases p, reflexivity },
    apply l
Defined.

  protectedDefinition elim_type (Pbase : Type) (Ploop : Pbase <~> Pbase)
    (x : S¹) : Type.
  circle.elim Pbase (ua Ploop) x

  protectedDefinition elim_type_on (x : S¹) (Pbase : Type)
    (Ploop : Pbase <~> Pbase) : Type.
  circle.elim_type Pbase Ploop x

Definition elim_type_loop (Pbase : Type) (Ploop : Pbase <~> Pbase) :
    transport (circle.elim_type Pbase Ploop) loop = Ploop.
  by rewrite [tr_eq_cast_ap_fn,↑circle.elim_type,elim_loop];apply cast_ua_fn

Definition elim_type_loop_inv (Pbase : Type) (Ploop : Pbase <~> Pbase) :
    transport (circle.elim_type Pbase Ploop) loop^-1 = to_inv Ploop.
  by rewrite [tr_inv_fn]; apply inv_eq_inv; apply elim_type_loop
Defined. circle











namespace circle
  open sigma
  (* universal property of the circle *)
Definition circle_pi_equiv (P : S¹ -> Type)
    : (forall (x : S¹), P x) <~> Σ(p : P base), p =[loop] p.
Proof.
    fapply equiv.MK,
    { intro f, exact ⟨f base, apd f loop⟩},
    { intro v x, induction v with p q, induction x,
      { exact p},
      { exact q}},
    { intro v, induction v with p q, fapply sigma_eq,
      { reflexivity},
      { esimp, apply pathover_idp_of_eq, apply rec_loop}},
    { intro f, apply eq_of_homotopy, intro x, induction x,
      { reflexivity},
      { apply eq_pathover_dep, apply hdeg_squareover, esimp, apply rec_loop}}
Defined.

Definition circle_arrow_equiv (P : Type)
    : (S¹ -> P) <~> Σ(p : P), p = p.
Proof.
    fapply equiv.MK,
    { intro f, exact ⟨f base, ap f loop⟩},
    { intro v x, induction v with p q, induction x,
      { exact p},
      { exact q}},
    { intro v, induction v with p q, fapply sigma_eq,
      { reflexivity},
      { esimp, apply pathover_idp_of_eq, apply elim_loop}},
    { intro f, apply eq_of_homotopy, intro x, induction x,
      { reflexivity},
      { apply eq_pathover, apply hdeg_square, esimp, apply elim_loop}}
Defined.

Definition pointed_circle [instance] : pointed S¹.
  pointed.mk base

Definition pcircle : pType . pointed.mk' S¹
  notation `S¹*` . pcircle

Definition loop_neq_idp : loop ≠ idp.
  assume H : loop = idp,
  have H2 : forall {A : Type₁} {a : A} {p : a = a}, p = idp,
    from fun A a p => calc
      p   = ap (circle.elim a p) loop : elim_loop
      ... = ap (circle.elim a p) (refl base) : by rewrite H,
  eq_bnot_ne_idp H2

Definition circle_turn (x : S¹) : x = x.
Proof.
    induction x,
    { exact loop },
    { apply eq_pathover, apply square_of_eq, rewrite ap_id }
Defined.

Definition turn_neq_idp : circle_turn ≠ (fun x => idp).
  assume H : circle_turn = fun x => idp,
  have H2 : loop = idp, from apd10 H base,
  absurd H2 loop_neq_idp

  open int

  protectedDefinition code (x : S¹) : Type₀.
  circle.elim_type_on x ℤ equiv_succ

Definition transport_code_loop (a : ℤ) : transport circle.code loop a = succ a.
  ap10 !elim_type_loop a

Definition transport_code_loop_inv (a : ℤ) : transport circle.code loop^-1 a = pred a.
  ap10 !elim_type_loop_inv a

  protectedDefinition encode {x : S¹} (p : base = x) : circle.code x.
  transport circle.code p (0 : ℤ)

  protectedDefinition decode {x : S¹} : circle.code x -> base = x.
Proof.
    induction x,
    { exact power loop},
    { apply arrow_pathover_left, intro b, apply eq_pathover_constant_left_id_right,
      apply square_of_eq, rewrite [idp_con, power_con,transport_code_loop]}
Defined.

Definition circle_eq_equiv (x : S¹) : (base = x) <~> circle.code x.
Proof.
    fapply equiv.MK,
    { exact circle.encode},
    { exact circle.decode},
    { exact abstract [irreducible] begin
      induction x,
      { intro a, esimp, apply rec_nat_on a,
        { exact idp},
        { intros n p, rewrite [↑circle.encode, -power_con, con_tr, transport_code_loop],
          exact ap succ p},
        { intros n p, rewrite [↑circle.encode, nat_succ_eq_int_succ, neg_succ, -power_con_inv,
            @con_tr _ circle.code, transport_code_loop_inv, ↑[circle.encode] at p, p, -neg_succ] }},
      { apply pathover_of_tr_eq, apply eq_of_homotopy, intro a, apply @is_set.elim,
        esimp, exact _} end end},
    { intro p, cases p, exact idp},
Defined.

Definition base_eq_base_equiv : base = base <~> ℤ.
  circle_eq_equiv base

Definition decode_add (a b : ℤ) : circle.decode (a +[ℤ] b) = circle.decode a @ circle.decode b.
  !power_con_power^-1

Definition encode_con (p q : base = base)
    : circle.encode (p @ q) = circle.encode p +[ℤ] circle.encode q.
  preserve_binary_of_inv_preserve base_eq_base_equiv concat (@add ℤ _) decode_add p q

  --the carrier of forall ₁(S¹) is the set-truncation of base = base.
  open algebra trunc group

Definition fg_carrier_equiv_int : forall [1](S¹*) <~> ℤ.
  trunc_equiv_trunc 0 base_eq_base_equiv @e @(trunc_equiv 0 ℤ) proof _ qed

Definition con_comm_base (p q : base = base) : p @ q = q @ p.
  eq_of_fn_eq_fn base_eq_base_equiv (by esimp;rewrite [+encode_con,add.comm])

Definition fundamental_group_of_circle : forall ₁(S¹*) <~>g gℤ.
Proof.
    apply (isomorphism_of_equiv fg_carrier_equiv_int),
    intros g h,
    induction g with g', induction h with h',
    apply encode_con,
Defined.

  open nat
Definition homotopy_group_of_circle (n : ℕ) : forall g[n+2] S¹* <~>g G0.
Proof.
    refine @trivial_homotopy_add_of_is_set_loopn S¹* 1 n _,
    apply is_trunc_equiv_closed_rev, apply base_eq_base_equiv
Defined.

Definition eq_equiv_Z (x : S¹) : x = x <~> ℤ.
Proof.
    induction x,
    { apply base_eq_base_equiv},
    { apply equiv_pathover, intro p p' q, apply pathover_of_eq,
      note H . eq_of_square (square_of_pathover q),
      rewrite con_comm_base at H,
      note H' . cancel_left _ H,
      induction H', reflexivity}
Defined.

  proposition is_trunc_circle [instance] : is_trunc 1 S¹.
Proof.
    apply is_trunc_succ_of_is_trunc_loop,
    { apply trunc_index.minus_one_le_succ},
    { intro x, apply is_trunc_equiv_closed_rev, apply eq_equiv_Z}
Defined.

  proposition is_conn_circle [instance] : is_conn 0 S¹.
  sphere.is_conn_sphere 1

Definition is_conn_pcircle [instance] : is_conn 0 S¹* . !is_conn_circle
Definition is_trunc_pcircle [instance] : is_trunc 1 S¹* . !is_trunc_circle

Definition circle_mul (x y : S¹) : S¹.
  circle.elim y (circle_turn y) x

Definition circle_mul_base (x : S¹) : circle_mul x base = x.
Proof.
    induction x,
    { reflexivity },
    { apply eq_pathover_id_right, apply hdeg_square, apply elim_loop }
Defined.

Definition circle_base_mul (x : S¹) : circle_mul base x = x.
  idp

  (*
    Suppose for `f, g : A -> B` we prove a homotopy `H : f == g` by induction on the element in `A`.
    And suppose `p : a = a'` is a path constructor in `A`.
    Then `natural_square_tr H p` has type `square (H a) (H a') (ap f p) (ap g p)` and is equal
    to the square which defined H on the path constructor
  *)

Definition natural_square_elim_loop {A : Type} {f g : S¹ -> A} (p : f base = g base)
    (q : square p p (ap f loop) (ap g loop))
    : natural_square (circle.rec p (eq_pathover q)) loop = q.
Proof.
    refine ap square_of_pathover !rec_loop @ _,
    exact to_right_inv !eq_pathover_equiv_square q
Defined.

Definition circle_elim_constant {A : Type} {a : A} {p : a = a} (r : p = idp) (x : S¹) :
    circle.elim a p x = a.
Proof.
    induction x,
    { reflexivity },
    { apply eq_pathover_constant_right, apply hdeg_square, exact !elim_loop @ r }
Defined.

Defined. circle
