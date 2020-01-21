(*
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Chain complexes.

We define chain complexes in a general way as a sequence X of types indexes over an arbitrary type
N with a successor S. There are maps X (S n) -> X n for n : N. We can vary N to have chain complexes
indexed by ℕ, ℤ, a finite type or something else, and for both ℕ and ℤ we can choose the maps to
go up or down. We also use the indexing ℕ \* 3 for the LES of homotopy groups, because then it
computes better (see [LES_of_homotopy_groups]).

We have two separate notions of
chain complexes:
- type_chain_complex: sequence of types, where exactness is formulated using pure existence.
- chain_complex: sequence of sets, where exactness is formulated using mere existence.

*)

import types.int algebra.group_theory types.fin types.unit

open eq pointed int unit is_equiv equiv is_trunc trunc function algebra group sigma.ops
     sum prod nat bool fin

structure succ_str : Type.
  (carrier : Type)
  (succ : carrier -> carrier)



Definition succ_str.S {X : succ_str} : X -> X . succ_str.succ X

open succ_str

Definition snat : succ_str . succ_str.mk ℕ nat.succ
Definition snat' : succ_str . succ_str.mk ℕ nat.pred
Definition sint : succ_str . succ_str.mk ℤ int.succ
Definition sint' : succ_str . succ_str.mk ℤ int.pred

notation `+ℕ` . snat
notation `-ℕ` . snat'
notation `+ℤ` . sint
notation `-ℤ` . sint'

Definition stratified_type (N : succ_str) (n : ℕ) : Type₀ . N \* fin (succ n)

Definition stratified_succ {N : succ_str} {n : ℕ} (x : stratified_type N n)
  : stratified_type N n.
(if val (pr2 x) = n then S (pr1 x) else pr1 x, cyclic_succ (pr2 x))

(* You might need to manually change the succ_str, to use predecessor as "successor" *)
Definition stratified_pred (N : succ_str) {n : ℕ} (x : stratified_type N n)
  : stratified_type N n.
(if val (pr2 x) = 0 then S (pr1 x) else pr1 x, cyclic_pred (pr2 x))

Definition stratified (N : succ_str) (n : ℕ) : succ_str.
succ_str.mk (stratified_type N n) stratified_succ

notation `+3ℕ` . stratified +ℕ 2
notation `-3ℕ` . stratified -ℕ 2
notation `+3ℤ` . stratified +ℤ 2
notation `-3ℤ` . stratified -ℤ 2
notation `+6ℕ` . stratified +ℕ 5
notation `-6ℕ` . stratified -ℕ 5
notation `+6ℤ` . stratified +ℤ 5
notation `-6ℤ` . stratified -ℤ 5

namespace succ_str
  protectedDefinition add {N : succ_str} (n : N) (k : ℕ) : N.
  iterate S k n

  infix ` +' `:65 . succ_str.add

Definition add_succ {N : succ_str} (n : N) (k : ℕ) : n +' (k + 1) = (S n) +' k.
  by induction k with k p; reflexivity; exact ap S p

Defined. succ_str

namespace chain_complex

  export [notation] succ_str

  (*
    We define "type chain complexes" which are chain complexes without the
    "set"-requirement. Exactness is formulated without propositional truncation.
  *)
  structure type_chain_complex (N : succ_str) : Type.
    (car : N -> pType)
    (fn : forall (n : N), car (S n) ->* car n)
    (is_chain_complex : forall (n : N) (x : car (S (S n))), fn n (fn (S n) x) = (point _))

  section
  variables {N : succ_str} (X : type_chain_complex N) (n : N)
Definition tcc_to_car [coercion] . @type_chain_complex.car
Definition tcc_to_fn  : X (S n) ->* X n . type_chain_complex.fn X n
Definition tcc_is_chain_complex  [unfold 2]
    : forall (x : X (S (S n))), tcc_to_fn X n (tcc_to_fn X (S n) x) = (point _).
  type_chain_complex.is_chain_complex X n

  (* important: these notions are shifted by one! (this is to avoid transports) *)
Definition is_exact_at_t (* X n *) : Type.
  forall (x : X (S n)), tcc_to_fn X n x = (point _) -> fiber (tcc_to_fn X (S n)) x

Definition is_exact_t (* X *) : Type.
  forall (n : N), is_exact_at_t X n

  (* A chain complex on +ℕ can be trivially extended to a chain complex on +ℤ *)
Definition type_chain_complex_from_left (X : type_chain_complex +ℕ)
    : type_chain_complex +ℤ.
  type_chain_complex.mk (int.rec X (fun n => punit))
    begin
      intro n, fconstructor,
      { induction n with n n,
        { exact tcc_to_fn X n},
        { esimp, intro x, exact star}},
      { induction n with n n,
        { apply point_eq},
        { reflexivity}}
    end
    begin
      intro n, induction n with n n,
      { exact tcc_is_chain_complex X n},
      { esimp, intro x, reflexivity}
    end

Definition is_exact_t_from_left {X : type_chain_complex +ℕ} {n : ℕ}
    (H : is_exact_at_t X n)
    : is_exact_at_t (type_chain_complex_from_left X) (of_nat n).
  H

  (*
    Given a natural isomorphism between a chain complex and any other sequence,
    we can give the other sequence the structure of a chain complex, which is exact at the
    positions where the original sequence is.
  *)
Definition transfer_type_chain_complex (* X *)
    {Y : N -> pType} (g : forall {n : N}, Y (S n) ->* Y n) (e : forall {n}, X n <~>* Y n)
    (p : forall {n} (x : X (S n)), e (tcc_to_fn X n x) = g (e x)) : type_chain_complex N.
  type_chain_complex.mk Y @g
    abstract begin
      intro n, apply equiv_rect (equiv_of_pequiv e), intro x,
      refine ap g (p x)^-1 @ _,
      refine (p _)^-1 @ _,
      refine ap e (tcc_is_chain_complex X n _) @ _,
      apply point_eq
    end end

Definition is_exact_at_t_transfer {X : type_chain_complex N} {Y : N -> pType}
    {g : forall {n : N}, Y (S n) ->* Y n} (e : forall {n}, X n <~>* Y n)
    (p : forall {n} (x : X (S n)), e (tcc_to_fn X n x) = g (e x)) {n : N}
    (H : is_exact_at_t X n) : is_exact_at_t (transfer_type_chain_complex X @g @e @p) n.
Proof.
    intro y q, esimp at *,
    have H2 : tcc_to_fn X n (e^-1ᵉ* y) = (point _),
    begin
      refine (inv_commute (fun n => equiv_of_pequiv e) _ _ @p _)^-1ᵖ @ _,
      refine ap _ q @ _,
      exact point_eq e^-1ᵉ*
    end,
    cases (H _ H2) with x r,
    refine fiber.mk (e x) _,
    refine (p x)^-1 @ _,
    refine ap e r @ _,
    apply right_inv
Defined.

  (*
    We want aDefinition which states that if we have a chain complex, but with some
    where the maps are composed by an equivalences, we want to remove this equivalence.
    The following twoDefinitions give sufficient conditions for when this is allowed.
    We use this to transform the LES of homotopy groups where on the odd levels we have
    maps -forall ₙ(...) into the LES of homotopy groups where we remove the minus signs (which
    represents composition with path inversion).
  *)
Definition type_chain_complex_cancel_aut (* X *)
    (g : forall {n : N}, X (S n) ->* X n) (e : forall {n}, X n <~>* X n)
    (r : forall {n}, X n ->* X n)
    (p : forall {n : N} (x : X (S n)), g (e x) = tcc_to_fn X n x)
    (pr : forall {n : N} (x : X (S n)), g x = r (g (e x))) : type_chain_complex N.
  type_chain_complex.mk X @g
    abstract begin
      have p' : forall {n : N} (x : X (S n)), g x = tcc_to_fn X n (e^-1 x),
      from fun n => homotopy_inv_of_homotopy_pre e _ _ p,
      intro n x,
      refine ap g !p' @ !pr @ _,
      refine ap r !p @ _,
      refine ap r (tcc_is_chain_complex X n _) @ _,
      apply point_eq
    end end

Definition is_exact_at_t_cancel_aut {X : type_chain_complex N}
    {g : forall {n : N}, X (S n) ->* X n} {e : forall {n}, X n <~>* X n}
    {r : forall {n}, X n ->* X n} (l : forall {n}, X n ->* X n)
    (p : forall {n : N} (x : X (S n)), g (e x) = tcc_to_fn X n x)
    (pr : forall {n : N} (x : X (S n)), g x = r (g (e x)))
    (pl : forall {n : N} (x : X (S n)), g (l x) = e (g x))
    (H : is_exact_at_t X n) : is_exact_at_t (type_chain_complex_cancel_aut X @g @e @r @p @pr) n.
Proof.
    intro y q, esimp at *,
    have H2 : tcc_to_fn X n (e^-1 y) = (point _),
    from (homotopy_inv_of_homotopy_pre e _ _ p _)^-1 @ q,
    cases (H _ H2) with x s,
    refine fiber.mk (l (e x)) _,
    refine !pl @ _,
    refine ap e (!p @ s) @ _,
    apply right_inv
Defined.

  (*
    A more general transferDefinition.
    Here the base type can also change by an equivalence.
  *)
Definition transfer_type_chain_complex2 {M : succ_str} {Y : M -> pType}
    (f : M <~> N) (c : forall (m : M), S (f m) = f (S m))
    (g : forall {m : M}, Y (S m) ->* Y m) (e : forall {m}, X (f m) <~>* Y m)
    (p : forall {m} (x : X (S (f m))), e (tcc_to_fn X (f m) x) = g (e (cast (ap (fun x => X x) (c m)) x)))
    : type_chain_complex M.
  type_chain_complex.mk Y @g
    abstract begin
      intro m,
      apply equiv_rect (equiv_of_pequiv e),
      apply equiv_rect (equiv_of_eq (ap (fun x => X x) (c (S m)))), esimp,
      apply equiv_rect (equiv_of_eq (ap (fun x => X (S x)) (c m))), esimp,
      intro x, refine ap g (p _)^-1 @ _,
      refine ap g (ap e (fn_cast_eq_cast_fn (c m) (fun n => pmap.to_fun (tcc_to_fn X n)) x)) @ _ =>
      refine (p _)^-1 @ _,
      refine ap e (tcc_is_chain_complex X (f m) _) @ _,
      apply point_eq
    end end

Definition is_exact_at_t_transfer2 {X : type_chain_complex N} {M : succ_str} {Y : M -> pType}
    (f : M <~> N) (c : forall (m : M), S (f m) = f (S m))
    (g : forall {m : M}, Y (S m) ->* Y m) (e : forall {m}, X (f m) <~>* Y m)
    (p : forall {m} (x : X (S (f m))), e (tcc_to_fn X (f m) x) = g (e (cast (ap (fun x => X x) (c m)) x)))
    {m : M} (H : is_exact_at_t X (f m))
    : is_exact_at_t (transfer_type_chain_complex2 X f c @g @e @p) m.
Proof.
    intro y q, esimp at *,
    have H2 : tcc_to_fn X (f m) ((equiv_of_eq (ap (fun x => X x) (c m)))^-1ᵉ (e^-1 y)) = (point _),
    begin
      refine _ @ ap e^-1ᵉ* q @ (point_eq (e^-1ᵉ*)), apply @eq_inv_of_eq _ _ e, clear q, revert y,
      apply inv_homotopy_of_homotopy_pre e,
      apply inv_homotopy_of_homotopy_pre, apply p
    end,
    induction (H _ H2) with x r,
    refine fiber.mk (e (cast (ap (fun x => X x) (c (S m))) (cast (ap (fun x => X (S x)) (c m)) x))) _,
    refine (p _)^-1 @ _,
    refine ap e (fn_cast_eq_cast_fn (c m) (fun n => pmap.to_fun (tcc_to_fn X n)) x) @ _ =>
    refine ap (fun x => e (cast _ x)) r @ _,
    esimp [equiv.symm], rewrite [-ap_inv],
    refine ap e !cast_cast_inv @ _,
    apply to_right_inv
Defined.

Defined.

  (* actual (set) chain complexes *)
  structure chain_complex (N : succ_str) : Type.
    (car : N -> Set*)
    (fn : forall (n : N), car (S n) ->* car n)
    (is_chain_complex : forall (n : N) (x : car (S (S n))), fn n (fn (S n) x) = (point _))

  section
  variables {N : succ_str} (X : chain_complex N) (n : N)

Definition cc_to_car [coercion] . @chain_complex.car
Definition cc_to_fn  : X (S n) ->* X n . @chain_complex.fn N X n
Definition cc_is_chain_complex  [unfold 2]
    : forall (x : X (S (S n))), cc_to_fn X n (cc_to_fn X (S n) x) = (point _).
  @chain_complex.is_chain_complex N X n

  (* important: these notions are shifted by one! (this is to avoid transports) *)
Definition is_exact_at (* X n *) : Type.
  forall (x : X (S n)), cc_to_fn X n x = (point _) -> image (cc_to_fn X (S n)) x

Definition is_exact (* X *) : Type . forall (n : N), is_exact_at X n

Definition chain_complex_from_left (X : chain_complex +ℕ) : chain_complex +ℤ.
  chain_complex.mk (int.rec X (fun n => punit))
    begin
      intro n, fconstructor,
      { induction n with n n,
        { exact cc_to_fn X n},
        { esimp, intro x, exact star}},
      { induction n with n n,
        { apply point_eq},
        { reflexivity}}
    end
    begin
      intro n, induction n with n n,
      { exact cc_is_chain_complex X n},
      { esimp, intro x, reflexivity}
    end

Definition is_exact_from_left {X : chain_complex +ℕ} {n : ℕ} (H : is_exact_at X n)
    : is_exact_at (chain_complex_from_left X) (of_nat n).
  H

Definition transfer_chain_complex {Y : N -> Set*}
    (g : forall {n : N}, Y (S n) ->* Y n) (e : forall {n}, X n <~>* Y n)
    (p : forall {n} (x : X (S n)), e (cc_to_fn X n x) = g (e x)) : chain_complex N.
  chain_complex.mk Y @g
    abstract begin
      intro n, apply equiv_rect (equiv_of_pequiv e), intro x,
      refine ap g (p x)^-1 @ _,
      refine (p _)^-1 @ _,
      refine ap e (cc_is_chain_complex X n _) @ _,
      apply point_eq
    end end

Definition is_exact_at_transfer {X : chain_complex N} {Y : N -> Set*}
    (g : forall {n : N}, Y (S n) ->* Y n) (e : forall {n}, X n <~>* Y n)
    (p : forall {n} (x : X (S n)), e (cc_to_fn X n x) = g (e x))
    {n : N} (H : is_exact_at X n) : is_exact_at (transfer_chain_complex X @g @e @p) n.
Proof.
    intro y q, esimp at *,
    have H2 : cc_to_fn X n (e^-1ᵉ* y) = (point _),
    begin
      refine (inv_commute (fun n => equiv_of_pequiv e) _ _ @p _)^-1ᵖ @ _,
      refine ap _ q @ _,
      exact point_eq e^-1ᵉ*
    end,
    induction (H _ H2) with x r,
    refine image.mk (e x) _,
    refine (p x)^-1 @ _,
    refine ap e r @ _,
    apply right_inv
Defined.

  (* A type chain complex can be set-truncated to a chain complex *)
Definition trunc_chain_complex (X : type_chain_complex N)
    : chain_complex N.
  chain_complex.mk
    (fun n => ptrunc 0 (X n))
    (fun n => ptrunc_functor 0 (tcc_to_fn X n))
    begin
      intro n x, esimp at *,
      refine @trunc.rec _ _ _ (fun H => !is_trunc_eq) _ x,
      clear x, intro x, esimp,
      exact ap tr (tcc_is_chain_complex X n x)
    end

Definition is_exact_at_trunc (X : type_chain_complex N) {n : N}
    (H : is_exact_at_t X n) : is_exact_at (trunc_chain_complex X) n.
Proof.
    intro x p, esimp at *,
    induction x with x, esimp at *,
    note q . !tr_eq_tr_equiv p,
    induction q with q,
    induction H x q with y r,
    refine image.mk (tr y) _,
    esimp, exact ap tr r
Defined.

Definition transfer_chain_complex2 {M : succ_str} {Y : M -> Set*}
    (f : N <~> M) (c : forall (n : N), f (S n) = S (f n))
    (g : forall {m : M}, pmap (Y (S m)) (Y m)) (e : forall {n}, X n <~>* Y (f n))
    (p : forall {n} (x : X (S n)), e (cc_to_fn X n x) = g (c n # e x)) : chain_complex M.
  chain_complex.mk Y @g
    begin
      refine equiv_rect f _ _, intro n,
      have H : forall (x : Y (f (S (S n)))), g (c n # g (c (S n) # x)) = (point _),
      begin
        apply equiv_rect (equiv_of_pequiv e), intro x,
        refine ap (fun x => g (c n # x)) (@p (S n) x)^-1ᵖ @ _,
        refine (p _)^-1 @ _,
        refine ap e (cc_is_chain_complex X n _) @ _,
        apply point_eq
      end,
      refine pi.pi_functor _ _ H =>
      { intro x, exact (c (S n))^-1 # (c n)^-1 # x}, (* with implicit arguments, this is: *)
      (* transport (fun x => Y x) (c (S n))^-1 (transport (fun x => Y (S x)) (c n)^-1 x) *)
      { intro x, intro p, refine _ @ p,
        rewrite [tr_inv_tr, fn_tr_eq_tr_fn (c n)^-1ᵖ (fun n => ppi.to_fun g) => tr_inv_tr]}
    end

Definition is_exact_at_transfer2 {X : chain_complex N} {M : succ_str} {Y : M -> Set*}
    (f : N <~> M) (c : forall (n : N), f (S n) = S (f n))
    (g : forall {m : M}, Y (S m) ->* Y m) (e : forall {n}, X n <~>* Y (f n))
    (p : forall {n} (x : X (S n)), e (cc_to_fn X n x) = g (c n # e x))
    {n : N} (H : is_exact_at X n) : is_exact_at (transfer_chain_complex2 X f c @g @e @p) (f n).
Proof.
    intro y q, esimp at *,
    have H2 : cc_to_fn X n (e^-1ᵉ* ((c n)^-1 # y)) = (point _),
    begin
      refine (inv_commute (fun n => equiv_of_pequiv e) _ _ @p _)^-1ᵖ @ _,
      rewrite [tr_inv_tr, q],
      exact point_eq e^-1ᵉ*
    end,
    induction (H _ H2) with x r,
    refine image.mk (c n # c (S n) # e x) _,
    rewrite [fn_tr_eq_tr_fn (c n) (fun n => ppi.to_fun g)] =>
    refine ap (fun x => c n # x) (p x)^-1 @ _,
    refine ap (fun x => c n # e x) r @ _,
    refine ap (fun x => c n # x) !right_inv @ _,
    apply tr_inv_tr,
Defined.

  (*
    This is a start of a development of chain complexes consisting only on groups.
    This might be useful to have in stable algebraic topology, but in the unstable case it's less
    useful, since the smallest terms usually don't have a group structure.
    We don't use it yet, so it's commented out for now
  *)
  (* structure group_chain_complex : Type . *)
  (*   (car : N -> Group) *)
  (*   (fn : forall (n : N), car (S n) ->g car n) *)
  (*   (is_chain_complex : forall {n : N} (x : car ((S n) + 1)), fn n (fn (S n) x) = 1) *)

  (* structure group_chain_complex : Type . (* chain complex on the naturals with maps going down *) *)
  (*   (car : N -> Group) *)
  (*   (fn : forall (n : N), car (S n) ->g car n) *)
  (*   (is_chain_complex : forall {n : N} (x : car ((S n) + 1)), fn n (fn (S n) x) = 1) *)

  (* structure right_group_chain_complex : Type . (* chain complex on the naturals with maps going up *) *)
  (*   (car : N -> Group) *)
  (*   (fn : forall (n : N), car n ->g car (S n)) *)
  (*   (is_chain_complex : forall {n : N} (x : car n), fn (S n) (fn n x) = 1) *)

  (*Definition  gcc_to_car [coercion] . @group_chain_complex.car *)
  (*Definition  gcc_to_fn             . @group_chain_complex.fn *)
  (*Definition  gcc_is_chain_complex  . @group_chain_complex.is_chain_complex *)
  (*Definition lgcc_to_car [coercion] . @left_group_chain_complex.car *)
  (*Definition lgcc_to_fn             . @left_group_chain_complex.fn *)
  (*Definition lgcc_is_chain_complex  . @left_group_chain_complex.is_chain_complex *)
  (*Definition rgcc_to_car [coercion] . @right_group_chain_complex.car *)
  (*Definition rgcc_to_fn             . @right_group_chain_complex.fn *)
  (*Definition rgcc_is_chain_complex  . @right_group_chain_complex.is_chain_complex *)

  (* (* important: these notions are shifted by one! (this is to avoid transports) *) *)
  (*Definition is_exact_at_g (X : group_chain_complex) (n : N) : Type . *)
  (* forall (x : X (S n)), gcc_to_fn X n x = 1 -> image (gcc_to_fn X (S n)) x *)
  (*Definition is_exact_at_lg (X : left_group_chain_complex) (n : N) : Type . *)
  (* forall (x : X (S n)), lgcc_to_fn X n x = 1 -> image (lgcc_to_fn X (S n)) x *)
  (*Definition is_exact_at_rg (X : right_group_chain_complex) (n : N) : Type . *)
  (* forall (x : X (S n)), rgcc_to_fn X (S n) x = 1 -> image (rgcc_to_fn X n) x *)

  (*Definition is_exact_g   (X : group_chain_complex) : Type . *)
  (* forall (n : N), is_exact_at_g X n *)
  (*Definition is_exact_lg (X : left_group_chain_complex) : Type . *)
  (* forall (n : N), is_exact_at_lg X n *)
  (*Definition is_exact_rg (X : right_group_chain_complex) : Type . *)
  (* forall (n : N), is_exact_at_rg X n *)

  (*Definition group_chain_complex_from_left (X : left_group_chain_complex) : group_chain_complex . *)
  (* group_chain_complex.mk (int.rec X (fun n => G0)) *)
  (*   begin *)
  (*     intro n, fconstructor, *)
  (*     { induction n with n n, *)
  (*       { exact @lgcc_to_fn X n}, *)
  (*       { esimp, intro x, exact star}}, *)
  (*     { induction n with n n, *)
  (*       { apply respect_mul}, *)
  (*       { intro g h, reflexivity}} *)
  (*   end *)
  (*   begin *)
  (*     intro n, induction n with n n, *)
  (*     { exact lgcc_is_chain_complex X}, *)
  (*     { esimp, intro x, reflexivity} *)
  (*   end *)

  (*Definition is_exact_g_from_left {X : left_group_chain_complex} {n : N} (H : is_exact_at_lg X n) *)
  (*   : is_exact_at_g (group_chain_complex_from_left X) n . *)
  (* H *)

  (*Definition transfer_left_group_chain_complex (X : left_group_chain_complex) *)
  (*   {Y : N -> Group} (g : forall {n : N}, Y (S n) ->g Y n) (e : forall {n}, X n <~>* Y n) *)
  (*   (p : forall {n} (x : X (S n)), e (lgcc_to_fn X n x) = g (e x)) : left_group_chain_complex . *)
  (* left_group_chain_complex.mk Y @g *)
  (*   begin *)
  (*     intro n, apply equiv_rect (pequiv_of_equiv e), intro x, *)
  (*     refine ap g (p x)^-1 @ _, *)
  (*     refine (p _)^-1 @ _, *)
  (*     refine ap e (lgcc_is_chain_complex X _) @ _, *)
  (*     exact point_eq *)
  (*   end *)

  (*Definition is_exact_at_t_transfer {X : left_group_chain_complex} {Y : N -> pType} *)
  (*   {g : forall {n : N}, Y (S n) ->* Y n} (e : forall {n}, X n <~>* Y n) *)
  (*   (p : forall {n} (x : X (S n)), e (lgcc_to_fn X n x) = g (e x)) {n : N} *)
  (*   (H : is_exact_at_lg X n) : is_exact_at_lg (transfer_left_group_chain_complex X @g @e @p) n . *)
  (* begin *)
  (*   intro y q, esimp at *, *)
  (*   have H2 : lgcc_to_fn X n (e^-1ᵉ* y) = (point _), *)
  (*   begin *)
  (*     refine (inv_commute (fun n => equiv_of_pequiv e) _ _ @p _)^-1ᵖ @ _, *)
  (*     refine ap _ q @ _, *)
  (*     exact point_eq e^-1ᵉ* *)
  (*   end, *)
  (*   cases (H _ H2) with x r, *)
  (*   refine image.mk (e x) _, *)
  (*   refine (p x)^-1 @ _, *)
  (*   refine ap e r @ _, *)
  (*   apply right_inv *)
  (* end *)

  (*
    The followingDefinitions state that in a chain complex, if certain types are contractible, and
    the chain complex is exact at the right spots, a map in the chain complex is an
    embedding/surjection/equivalence. For the first and third we also need to assume that
    the map is a group homomorphism (and hence that the two types around it are groups).
  *)

Definition is_embedding_of_trivial (X : chain_complex N) {n : N}
    (H : is_exact_at X n) [HX : is_contr (X (S (S n)))]
    [pgroup (X n)] [pgroup (X (S n))] [is_mul_hom (cc_to_fn X n)]
      : is_embedding (cc_to_fn X n).
Proof.
    apply is_embedding_of_is_mul_hom,
    intro g p,
    induction H g p with x q,
    have r : (point _) = x, from !is_prop.elim,
    induction r,
    refine q^-1 @ _,
    apply point_eq
Defined.

Definition is_surjective_of_trivial (X : chain_complex N) {n : N}
    (H : is_exact_at X n) [HX : is_contr (X n)] : is_surjective (cc_to_fn X (S n)).
Proof.
    intro g,
    refine trunc.elim _ (H g !is_prop.elim),
    apply tr
Defined.

Definition is_equiv_of_trivial (X : chain_complex N) {n : N}
    (H1 : is_exact_at X n) (H2 : is_exact_at X (S n))
    [HX1 : is_contr (X n)] [HX2 : is_contr (X (S (S (S n))))]
    [pgroup (X (S n))] [pgroup (X (S (S n)))] [is_mul_hom (cc_to_fn X (S n))]
    : is_equiv (cc_to_fn X (S n)).
Proof.
    apply is_equiv_of_is_surjective_of_is_embedding,
    { apply is_embedding_of_trivial X, apply H2},
    { apply is_surjective_of_trivial X, apply H1},
Defined.

Definition is_contr_of_is_embedding_of_is_surjective {N : succ_str} (X : chain_complex N) {n : N}
    (H : is_exact_at X (S n)) [is_embedding (cc_to_fn X n)]
    [H2 : is_surjective (cc_to_fn X (S (S (S n))))] : is_contr (X (S (S n))).
Proof.
    apply is_contr.mk (point _), intro x,
    have p : cc_to_fn X n (cc_to_fn X (S n) x) = cc_to_fn X n (point _),
      from !cc_is_chain_complex @ !point_eq^-1,
    have q : cc_to_fn X (S n) x = (point _), from is_injective_of_is_embedding p,
    induction H x q with y r,
    induction H2 y with z s,
    exact (cc_is_chain_complex X _ z)^-1 @ ap (cc_to_fn X _) s @ r
Defined.

Defined.

Defined. chain_complex
