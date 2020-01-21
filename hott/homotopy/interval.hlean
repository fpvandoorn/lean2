(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the interval
*)

import .susp types.eq types.prod cubical.square
open eq susp unit equiv is_trunc nat prod pointed

Definition interval : Type₀ . susp unit

namespace interval

Definition zero : interval . north
Definition one  : interval . south
Definition seg  : zero = one . merid star

  protectedDefinition rec {P : interval -> Type} (P0 : P zero) (P1 : P one)
    (Ps : P0 =[seg] P1) (x : interval) : P x.
Proof.
    fapply susp.rec_on x,
    { exact P0},
    { exact P1},
    { intro x, cases x, exact Ps}
Defined.

  protectedDefinition rec_on {P : interval -> Type} (x : interval)
    (P0 : P zero) (P1 : P one) (Ps : P0 =[seg] P1) : P x.
  interval.rec P0 P1 Ps x

Definition rec_seg {P : interval -> Type} (P0 : P zero) (P1 : P one) (Ps : P0 =[seg] P1)
      : apd (interval.rec P0 P1 Ps) seg = Ps.
  !rec_merid

  protectedDefinition elim {P : Type} (P0 P1 : P) (Ps : P0 = P1) (x : interval) : P.
  interval.rec P0 P1 (pathover_of_eq _ Ps) x

  protectedDefinition elim_on {P : Type} (x : interval) (P0 P1 : P)
    (Ps : P0 = P1) : P.
  interval.elim P0 P1 Ps x

Definition elim_seg {P : Type} (P0 P1 : P) (Ps : P0 = P1)
    : ap (interval.elim P0 P1 Ps) seg = Ps.
Proof.
    apply eq_of_fn_eq_fn_inv !(pathover_constant seg),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑interval.elim,rec_seg],
Defined.

  protectedDefinition elim_type (P0 P1 : Type) (Ps : P0 <~> P1) (x : interval) : Type.
  interval.elim P0 P1 (ua Ps) x

  protectedDefinition elim_type_on (x : interval) (P0 P1 : Type) (Ps : P0 <~> P1)
    : Type.
  interval.elim_type P0 P1 Ps x

Definition elim_type_seg (P0 P1 : Type) (Ps : P0 <~> P1)
    : transport (interval.elim_type P0 P1 Ps) seg = Ps.
  by rewrite [tr_eq_cast_ap_fn,↑interval.elim_type,elim_seg];apply cast_ua_fn

Definition is_contr_interval [instance] [priority 900] : is_contr interval.
  is_contr.mk zero (fun x => interval.rec_on x idp seg !eq_pathover_r_idp)

Definition naive_funext_of_interval : naive_funext.
  fun A P f g p => ap (fun (i : interval) (x : A) => interval.elim_on i (f x) (g x) (p x)) seg

Definition funext_of_interval : funext.
  funext_from_naive_funext naive_funext_of_interval

Defined. interval open interval

Definition cube : ℕ -> Type₀
| cube 0        . unit
| cube (succ n) . cube n \* interval

abbreviation square . cube (succ (succ nat.zero))

Definition cube_one_equiv_interval : cube 1 <~> interval.
!prod_comm_equiv @e !prod_unit_equiv


Definition prod_square {A B : Type} {a a' : A} {b b' : B} (p : a = a') (q : b = b')
  : square (pair_eq p idp) (pair_eq p idp) (pair_eq idp q) (pair_eq idp q).
by cases p; cases q; exact ids

namespace square

Definition tl : square . (star, zero, zero)
Definition tr : square . (star, one,  zero)
Definition bl : square . (star, zero, one )
Definition br : square . (star, one,  one )
  (* s stands for "square" in the followingDefinitions *)
Definition st : tl = tr . pair_eq (pair_eq idp seg) idp
Definition sb : bl = br . pair_eq (pair_eq idp seg) idp
Definition sl : tl = bl . pair_eq idp seg
Definition sr : tr = br . pair_eq idp seg
Definition sfill : square st sb sl sr . !prod_square
Definition fill : st @ sr = sl @ sb . !square_equiv_eq sfill

Defined. square
