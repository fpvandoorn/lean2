(*
Copyright (c) 2016 Ulrik Buchholtz and Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke

H-spaces and the Hopf construction
*)

import types.equiv .wedge .join

open eq eq.ops equiv is_equiv is_conn is_trunc trunc susp join pointed

namespace hopf

structure h_space [class] (A : Type) extends has_mul A, has_one A.
(one_mul : ∀a, mul one a = a) (mul_one : ∀a, mul a one = a)

section
  variable {A : Type}
  variable [H : h_space A]
  include H

Definition one_mul (a : A) : 1 * a = a . !h_space.one_mul
Definition mul_one (a : A) : a * 1 = a . !h_space.mul_one

Definition h_space_equiv_closed {B : Type} (f : A <~> B) : h_space B.
  ( h_space, one . f 1, mul . (fun b b' => f (f^-1 b * f^-1 b')),
    one_mul . by intro b; rewrite [to_left_inv,one_mul,to_right_inv],
    mul_one . by intro b; rewrite [to_left_inv,mul_one,to_right_inv] )

  (* Lemma 8.5.5.
     If A is 0-connected, then left and right multiplication are equivalences *)
  variable [K : is_conn 0 A]
  include K

Definition is_equiv_mul_left [instance] : forall (a : A), is_equiv (fun x => a * x).
Proof.
    apply is_conn_fun.elim -1 (is_conn_fun_from_unit -1 A 1)
                           (fun a => trunctype.mk' -1 (is_equiv (fun x => a * x))),
    intro z, change is_equiv (fun x : A => 1 * x), apply is_equiv.homotopy_closed id,
    intro x, apply inverse, apply one_mul
Defined.

Definition is_equiv_mul_right [instance]  : forall (a : A), is_equiv (fun x => x * a).
Proof.
    apply is_conn_fun.elim -1 (is_conn_fun_from_unit -1 A 1)
                           (fun a => trunctype.mk' -1 (is_equiv (fun x => x * a))),
    intro z, change is_equiv (fun x : A => x * 1), apply is_equiv.homotopy_closed id,
    intro x, apply inverse, apply mul_one
Defined.
Defined.

section
  variable (A : Type)
  variables [H : h_space A] [K : is_conn 0 A]
  include H K

Definition hopf : susp A -> Type.
  susp.elim_type A A (fun a => equiv.mk (fun x => a * x) !is_equiv_mul_left)

 (* Lemma 8.5.7. The total space is A * A *)
  open prod prod.ops

  protectedDefinition total : sigma (hopf A) <~> join A A.
Proof.
    apply equiv.trans (susp.flattening A A A _), unfold join,
    apply equiv.trans (pushout.symm pr₂ (fun z : A \* A => z.1 * z.2)),
    fapply pushout.equiv,
    { fapply equiv.MK
             (fun z : A \* A => (z.1 * z.2, z.2))
             (fun z : A \* A => ((fun x => x * z.2)^-1 z.1, z.2)),
      { intro z, induction z with u v, esimp,
        exact prod_eq (right_inv (fun x => x * v) u) idp },
      { intro z, induction z with a b, esimp,
        exact prod_eq (left_inv (fun x => x * b) a) idp } },
    { reflexivity },
    { reflexivity },
    { reflexivity },
    { reflexivity }
Defined.
Defined.

(* If A is a K(G,1), then A is deloopable.
   Main lemma of Licata-Finster. *)
section
  parameters (A : Type) [T : is_trunc 1 A] [K : is_conn 0 A] [H : h_space A]
             (coh : one_mul 1 = mul_one 1 :> (1 * 1 = 1 :> A))
Definition P : susp A -> Type.
  fun x => trunc 1 (north = x)

  include K H T

  local abbreviation codes : susp A -> Type . hopf A

Definition transport_codes_merid (a a' : A)
    : transport codes (merid a) a' = a * a' :> A.
  ap10 (elim_type_merid _ _ _ a) a'

Definition is_trunc_codes [instance] (x : susp A) : is_trunc 1 (codes x).
Proof.
    induction x with a, do 2 apply T, apply is_prop.elimo
Defined.

Definition encode₀ {x : susp A} : north = x -> codes x.
  fun p => transport codes p (by change A; exact 1)

Definition encode {x : susp A} : P x -> codes x.
  fun p => trunc.elim encode₀ p

Definition decode' : A -> P (@north A).
  fun a => tr (merid a @ (merid 1)^-1)

Definition transport_codes_merid_one_inv (a : A)
    : transport codes (merid 1)^-1 a = a.
  ap10 (elim_type_merid_inv _ _ _ 1) a @ begin apply to_inv_eq_of_eq, esimp, refine !one_mul^-1 end

  proposition encode_decode' (a : A) : encode (decode' a) = a.
Proof.
    esimp [encode, decode', encode₀],
    refine !con_tr @ _,
    refine (ap (transport _ _) !transport_codes_merid @ !transport_codes_merid_one_inv) @ _,
    apply mul_one
Defined.

  include coh

  open pointed

  proposition homomorphism : forall a a' : A,
    tr (merid (a * a')) = tr (merid a' @ (merid 1)^-1 @ merid a)
      :> trunc 1 (@north A = @south A).
Proof.
    fapply @wedge_extension.ext (pointed.MK A 1) (pointed.MK A 1) 0 0 K K
      (fun a a' : A => tr (merid (a * a')) = tr (merid a' @ (merid 1)^-1 @ merid a)),
    { intros a a', apply is_trunc_eq, apply is_trunc_trunc },
    { change forall a : A,
             tr (merid (a * 1)) = tr (merid 1 @ (merid 1)^-1 @ merid a)
             :> trunc 1 (@north A = @south A),
      intro a, apply ap tr,
      exact calc
        merid (a * 1) = merid a : ap merid (mul_one a)
                  ... = merid 1 @ (merid 1)^-1 @ merid a
        : (idp_con (merid a))^-1
          @ ap (fun w => w @ merid a) (con.right_inv (merid 1))^-1 },
    { change forall a' : A,
             tr (merid (1 * a')) = tr (merid a' @ (merid 1)^-1 @ merid 1)
             :> trunc 1 (@north A = @south A),
      intro a', apply ap tr,
      exact calc
        merid (1 * a') = merid a' : ap merid (one_mul a')
                   ... = merid a' @ (merid 1)^-1 @ merid 1
        : ap (fun w => merid a' @ w) (con.left_inv (merid 1))^-1
        @ (con.assoc' (merid a') (merid 1)^-1 (merid 1)) },
    { apply ap02 tr, esimp, fapply concat2,
      { apply ap02 merid, exact coh^-1 },
      { assert e : forall (X : Type)(x y : X)(p : x = y),
               (idp_con p)^-1 @ ap (fun w : x = x => w @ p) (con.right_inv p)^-1
               = ap (concat p) (con.left_inv p)^-1 @ con.assoc' p p^-1 p,
        { intros X x y p, cases p, reflexivity },
        apply e } }
Defined.

Definition decode {x : susp A} : codes x -> P x.
Proof.
    induction x,
    { exact decode' },
    { exact (fun a => tr (merid a)) },
    { apply pi.arrow_pathover_left, esimp, intro a',
      apply pathover_of_tr_eq, krewrite susp.elim_type_merid, esimp,
      krewrite [trunc_transport,eq_transport_r], apply inverse,
      apply homomorphism }
Defined.

Definition decode_encode {x : susp A} : forall t : P x, decode (encode t) = t.
Proof.
    apply trunc.rec, intro p, cases p, apply ap tr, apply con.right_inv
Defined.

  (*
     We define main_lemma by first defining its inverse, because normally equiv.MK changes
     the left_inv-component of an equivalence to adjointify it, but in this case we want the
     left_inv-component to be encode_decode'. So we adjointify its inverse, so that only the
     right_inv-component is changed.
  *)
Definition main_lemma : trunc 1 (north = north :> susp A) <~> A.
  (equiv.MK decode' encode decode_encode encode_decode')^-1ᵉ

Definition main_lemma_point
    : ptrunc 1 (Ω(susp A)) <~>* pointed.MK A 1.
  pointed.pequiv_of_equiv main_lemma idp

  protectedDefinition delooping : loops (ptrunc 2 (susp A)) <~>* pointed.MK A 1.
  loop_ptrunc_pequiv 1 (susp A) @e* main_lemma_point

  (* characterization of the underlying pointed maps *)
Definition to_pmap_main_lemma_point_pinv
    : main_lemma_point^-1ᵉ* ==* !ptr o* loop_susp_unit (pointed.MK A 1).
Proof.
    fapply Build_pHomotopy,
    { intro a, reflexivity },
    { reflexivity }
Defined.

Definition to_pmap_delooping_pinv :
    delooping^-1ᵉ* ==* Ω-> !ptr o* loop_susp_unit (pointed.MK A 1).
Proof.
    refine !trans_pinv @* _,
    refine pwhisker_left _ !to_pmap_main_lemma_point_pinv @* _,
    refine !passoc^-1* @* _,
    refine pwhisker_right _ !ap1_ptr^-1*,
Defined.

Definition hopf_delooping_elim {B : pType} (f : pointed.MK A 1 ->* loops B) [H2 : is_trunc 2 B] :
    Ω->(ptrunc.elim 2 (susp_elim f)) o* (hopf.delooping A coh)^-1ᵉ* ==* f.
Proof.
    refine pwhisker_left _ !to_pmap_delooping_pinv @* _,
    refine !passoc^-1* @* _,
    refine pwhisker_right _ (!ap1_pcompose^-1* @* ap1_phomotopy !ptrunc_elim_ptr) @* _,
    apply ap1_susp_elim
Defined.

Defined.

Defined. hopf
