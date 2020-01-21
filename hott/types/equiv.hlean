(*
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about the types equiv and is_equiv
*)

import .fiber .arrow arity ..prop_trunc cubical.square .pointed

open eq is_trunc sigma sigma.ops pi fiber function equiv

namespace is_equiv
  variables {A B : Type} (f : A -> B) [H : is_equiv f]
  include H
  (* is_equiv f is a mere proposition *)
Definition is_contr_fiber_of_is_equiv [instance] (b : B) : is_contr (fiber f b).
  is_contr.mk
    (fiber.mk (f^-1 b) (right_inv f b))
    (fun z => fiber.rec_on z (fun a p =>
      fiber_eq ((ap f^-1 p)^-1 @ left_inv f a) (calc
        right_inv f b = (ap (f o f^-1) p)^-1 @ ((ap (f o f^-1) p) @ right_inv f b)
                                                           : by rewrite inv_con_cancel_left
      ... = (ap (f o f^-1) p)^-1 @ (right_inv f (f a) @ p)   : by rewrite ap_con_eq_con
      ... = (ap (f o f^-1) p)^-1 @ (ap f (left_inv f a) @ p) : by rewrite [adj f]
      ... = (ap (f o f^-1) p)^-1 @ ap f (left_inv f a) @ p   : by rewrite con.assoc
      ... = (ap f (ap f^-1 p))^-1 @ ap f (left_inv f a) @ p  : by rewrite ap_compose
      ... = ap f (ap f^-1 p)^-1 @ ap f (left_inv f a) @ p    : by rewrite ap_inv
      ... = ap f ((ap f^-1 p)^-1 @ left_inv f a) @ p         : by rewrite ap_con)))

Definition is_contr_right_inverse : is_contr (Σ(g : B -> A), f o g == id).
Proof.
    fapply is_trunc_equiv_closed,
      {apply sigma_equiv_sigma_right, intro g, apply eq_equiv_homotopy},
    fapply is_trunc_equiv_closed,
      {apply fiber.sigma_char},
    fapply is_contr_fiber_of_is_equiv,
    apply (to_is_equiv (arrow_equiv_arrow_right B (equiv.mk f H))),
Defined.

Definition is_contr_right_coherence (u : Σ(g : B -> A), f o g == id)
    : is_contr (Σ(η : u.1 o f == id), forall (a : A), u.2 (f a) = ap f (η a)).
Proof.
    fapply is_trunc_equiv_closed,
      {apply equiv.symm, apply sigma_pi_equiv_pi_sigma},
    fapply is_trunc_equiv_closed,
      {apply pi_equiv_pi_right, intro a,
        apply (fiber_eq_equiv (fiber.mk (u.1 (f a)) (u.2 (f a))) (fiber.mk a idp))},
Defined.

  omit H

  protectedDefinition sigma_char : (is_equiv f) <~>
  (Σ(g : B -> A) (ε : f o g == id) (η : g o f == id), forall (a : A), ε (f a) = ap f (η a)).
  equiv.MK (fun H => ⟨inv f, right_inv f, left_inv f, adj f⟩)
           (fun p => is_equiv.mk f p.1 p.2.1 p.2.2.1 p.2.2.2)
           (fun p => begin
                  induction p with p1 p2,
                  induction p2 with p21 p22,
                  induction p22 with p221 p222,
                  reflexivity
                end)
           (fun H => by induction H; reflexivity)

  protectedDefinition sigma_char' : (is_equiv f) <~>
  (Σ(u : Σ(g : B -> A), f o g == id) (η : u.1 o f == id), forall (a : A), u.2 (f a) = ap f (η a)).
  calc
    (is_equiv f) <~>
      (Σ(g : B -> A) (ε : f o g == id) (η : g o f == id), forall (a : A), ε (f a) = ap f (η a))
          : is_equiv.sigma_char
    ... <~> (Σ(u : Σ(g : B -> A), f o g == id), Σ(η : u.1 o f == id), forall (a : A), u.2 (f a) = ap f (η a))
          : sigma_assoc_equiv (fun u => Σ(η : u.1 o f == id), forall (a : A), u.2 (f a) = ap f (η a))

  local attribute is_contr_right_inverse [instance] [priority 1600]
  local attribute is_contr_right_coherence [instance] [priority 1600]

Definition is_prop_is_equiv [instance] : is_prop (is_equiv f).
  is_prop_of_imp_is_contr
    (fun (H : is_equiv f) => is_trunc_equiv_closed -2 (equiv.symm !is_equiv.sigma_char'))

Definition inv_eq_inv {A B : Type} {f f' : A -> B} {Hf : is_equiv f} {Hf' : is_equiv f'}
    (p : f = f') : f^-1 = f'^-1.
  apd011 inv p !is_prop.elimo

  (* contractible fibers *)
Definition is_contr_fun_of_is_equiv [H : is_equiv f] : is_contr_fun f.
  is_contr_fiber_of_is_equiv f

Definition is_prop_is_contr_fun (f : A -> B) : is_prop (is_contr_fun f) . _

Definition is_equiv_of_is_contr_fun [H : is_contr_fun f] : is_equiv f.
  adjointify _ (fun b => point (center (fiber f b)))
               (fun b => point_eq (center (fiber f b)))
               (fun a => ap point (center_eq (fiber.mk a idp)))

Definition is_equiv_of_imp_is_equiv (H : B -> is_equiv f) : is_equiv f.
  @is_equiv_of_is_contr_fun _ _ f (fun b => @is_contr_fiber_of_is_equiv _ _ _ (H b) _)

Definition is_equiv_equiv_is_contr_fun : is_equiv f <~> is_contr_fun f.
  equiv_of_is_prop _ (fun H => !is_equiv_of_is_contr_fun)

Definition inv_commute'_fn {A : Type} {B C : A -> Type} (f : forall {a}, B a -> C a) [H : forall a, is_equiv (@f a)]
    {g : A -> A} (h : forall {a}, B a -> B (g a)) (h' : forall {a}, C a -> C (g a))
    (p : forall (a : A) (b : B a), f (h b) = h' (f b)) {a : A} (b : B a) :
    inv_commute' @f @h @h' p (f b)
      = (ap f^-1 (p b))^-1 @ left_inv f (h b) @ (ap h (left_inv f b))^-1.
Proof.
    rewrite [↑[inv_commute',eq_of_fn_eq_fn'],+ap_con,-adj_inv f,+con.assoc,inv_con_cancel_left,
       adj f,+ap_inv,-+ap_compose,
       eq_bot_of_square (natural_square_tr (fun b => (left_inv f (h b))^-1 @ ap f^-1 (p b)) (left_inv f b))^-1ʰ,
       con_inv,inv_inv,+con.assoc],
    do 3 apply whisker_left,
    rewrite [con_inv_cancel_left,con.left_inv]
Defined.

Defined. is_equiv

(* Moving equivalences around in homotopies *)
namespace is_equiv
  variables {A B C : Type} (f : A -> B) [Hf : is_equiv f]

  include Hf

  section pre_compose
    variables (α : A -> C) (β : B -> C)

    (* homotopy_inv_of_homotopy_pre is in init.equiv *)
    protectedDefinition inv_homotopy_of_homotopy_pre.is_equiv
      : is_equiv (inv_homotopy_of_homotopy_pre f α β).
    adjointify _ (homotopy_of_inv_homotopy_pre f α β)
    abstract begin
      intro q, apply eq_of_homotopy, intro b,
      unfold inv_homotopy_of_homotopy_pre,
      unfold homotopy_of_inv_homotopy_pre,
      apply inverse, apply eq_bot_of_square,
      apply eq_hconcat (ap02 α (adj_inv f b)),
      apply eq_hconcat (ap_compose α f^-1 (right_inv f b))^-1,
      apply natural_square q (right_inv f b)
    end end
    abstract begin
      intro p, apply eq_of_homotopy, intro a,
      unfold inv_homotopy_of_homotopy_pre,
      unfold homotopy_of_inv_homotopy_pre,
      apply trans (con.assoc
        (ap α (left_inv f a))^-1
        (p (f^-1 (f a)))
        (ap β (right_inv f (f a))))^-1,
      apply inverse, apply eq_bot_of_square,
      refine hconcat_eq _ (ap02 β (adj f a))^-1,
      refine hconcat_eq _ (ap_compose β f (left_inv f a)),
      apply natural_square p (left_inv f a)
    end end
Defined. pre_compose

  section post_compose
    variables (α : C -> A) (β : C -> B)

    (* homotopy_inv_of_homotopy_post is in init.equiv *)
    protectedDefinition inv_homotopy_of_homotopy_post.is_equiv
      : is_equiv (inv_homotopy_of_homotopy_post f α β).
    adjointify _ (homotopy_of_inv_homotopy_post f α β)
    abstract begin
      intro q, apply eq_of_homotopy, intro c,
      unfold inv_homotopy_of_homotopy_post,
      unfold homotopy_of_inv_homotopy_post,
      apply trans (whisker_right (left_inv f (α c))
       (ap_con f^-1 (right_inv f (β c))^-1 (ap f (q c))
       @ whisker_right (ap f^-1 (ap f (q c)))
       (ap_inv f^-1 (right_inv f (β c))))),
      apply inverse, apply eq_bot_of_square,
      apply eq_hconcat (adj_inv f (β c))^-1,
      apply eq_vconcat (ap_compose f^-1 f (q c))^-1,
      refine vconcat_eq _ (ap_id (q c)),
      apply natural_square_tr (left_inv f) (q c)
    end end
    abstract begin
      intro p, apply eq_of_homotopy, intro c,
      unfold inv_homotopy_of_homotopy_post,
      unfold homotopy_of_inv_homotopy_post,
      apply trans (whisker_left (right_inv f (β c))^-1
        (ap_con f (ap f^-1 (p c)) (left_inv f (α c)))),
      apply trans (con.assoc (right_inv f (β c))^-1 (ap f (ap f^-1 (p c)))
        (ap f (left_inv f (α c))))^-1,
      apply inverse, apply eq_bot_of_square,
      refine hconcat_eq _ (adj f (α c)),
      apply eq_vconcat (ap_compose f f^-1 (p c))^-1,
      refine vconcat_eq _ (ap_id (p c)),
      apply natural_square_tr (right_inv f) (p c)
    end end

Defined. post_compose

Defined. is_equiv

namespace is_equiv

  (* Theorem 4.7.7 *)
  variables {A : Type} {P Q : A -> Type}
  variable (f : forall a, P a -> Q a)

Definition is_fiberwise_equiv . forall a, is_equiv (f a)

Definition is_equiv_total_of_is_fiberwise_equiv [H : is_fiberwise_equiv f] : is_equiv (total f).
  is_equiv_sigma_functor id f

Definition is_fiberwise_equiv_of_is_equiv_total [H : is_equiv (total f)]
    : is_fiberwise_equiv f.
Proof.
    intro a,
    apply is_equiv_of_is_contr_fun => intro q,
    apply @is_contr_equiv_closed _ _ (fiber_total_equiv f q)
Defined.

Defined. is_equiv

namespace equiv
  open is_equiv
  variables {A B C : Type}

Definition equiv_mk_eq {f f' : A -> B} [H : is_equiv f] [H' : is_equiv f'] (p : f = f')
      : equiv.mk f H = equiv.mk f' H'.
  apd011 equiv.mk p !is_prop.elimo

Definition equiv_eq' {f f' : A <~> B} (p : to_fun f = to_fun f') : f = f'.
  by (cases f; cases f'; apply (equiv_mk_eq p))

Definition equiv_eq {f f' : A <~> B} (p : to_fun f == to_fun f') : f = f'.
  by apply equiv_eq'; apply eq_of_homotopy p

Definition trans_symm (f : A <~> B) (g : B <~> C) : (f @e g)^-1ᵉ = g^-1ᵉ @e f^-1ᵉ :> (C <~> A).
  equiv_eq' idp

Definition symm_symm (f : A <~> B) : f^-1ᵉ^-1ᵉ = f :> (A <~> B).
  equiv_eq' idp

  protectedDefinition equiv.sigma_char
    (A B : Type) : (A <~> B) <~> Σ(f : A -> B), is_equiv f.
Proof.
    fapply equiv.MK,
      {intro F, exact ⟨to_fun F => to_is_equiv F⟩},
      {intro p, cases p with f H, exact (equiv.mk f H)},
      {intro p, cases p, exact idp},
      {intro F, cases F, exact idp},
Defined.

Definition equiv_eq_char (f f' : A <~> B) : (f = f') <~> (to_fun f = to_fun f').
  calc
    (f = f') <~> (to_fun !equiv.sigma_char f = to_fun !equiv.sigma_char f')
                : eq_equiv_fn_eq (to_fun !equiv.sigma_char)
         ... <~> ((to_fun !equiv.sigma_char f).1 = (to_fun !equiv.sigma_char f').1 ) : equiv_subtype
         ... <~> (to_fun f = to_fun f') : equiv.rfl

Definition is_equiv_ap_to_fun (f f' : A <~> B)
    : is_equiv (ap to_fun : f = f' -> to_fun f = to_fun f').
Proof.
    fapply adjointify,
      {intro p, cases f with f H, cases f' with f' H', cases p, apply ap (mk f'), apply is_prop.elim},
      {intro p, cases f with f H, cases f' with f' H', cases p,
        apply @concat _ _ (ap to_fun (ap (equiv.mk f') (is_prop.elim H H'))) => {apply idp},
        generalize is_prop.elim H H', intro q, cases q, apply idp},
      {intro p, cases p, cases f with f H, apply ap (ap (equiv.mk f)), apply is_set.elim}
Defined.

Definition equiv_pathover {A : Type} {a a' : A} (p : a = a')
    {B : A -> Type} {C : A -> Type} (f : B a <~> C a) (g : B a' <~> C a')
    (r : forall (b : B a) (b' : B a') (q : b =[p] b'), f b =[p] g b') : f =[p] g.
Proof.
    fapply pathover_of_fn_pathover_fn,
    { intro a, apply equiv.sigma_char},
    { fapply sigma_pathover,
        esimp, apply arrow_pathover, exact r,
        apply is_prop.elimo}
Defined.

Definition is_contr_equiv (A B : Type) [HA : is_contr A] [HB : is_contr B] : is_contr (A <~> B).
Proof.
    apply @is_contr_of_inhabited_prop, apply is_prop.mk,
    intro x y, cases x with fx Hx, cases y with fy Hy, generalize Hy,
    apply (eq_of_homotopy (fun a => !eq_of_is_contr)) # (fun Hy => !is_prop.elim # rfl),
    apply equiv_of_is_contr_of_is_contr
Defined.

Definition is_trunc_succ_equiv (n : trunc_index) (A B : Type)
  [HA : is_trunc n.+1 A] [HB : is_trunc n.+1 B] : is_trunc n.+1 (A <~> B).
  @is_trunc_equiv_closed _ _ n.+1 (equiv.symm !equiv.sigma_char)
  (@is_trunc_sigma _ _ _ _ (fun f => !is_trunc_succ_of_is_prop))

Definition is_trunc_equiv (n : trunc_index) (A B : Type)
  [HA : is_trunc n A] [HB : is_trunc n B] : is_trunc n (A <~> B).
  by cases n; apply !is_contr_equiv; apply !is_trunc_succ_equiv

Definition eq_of_fn_eq_fn'_idp {A B : Type} (f : A -> B) [is_equiv f] (x : A)
    : eq_of_fn_eq_fn' f (idpath (f x)) = idpath x.
  (con_Vp _)

Definition eq_of_fn_eq_fn'_con {A B : Type} (f : A -> B) [is_equiv f] {x y z : A}
    (p : f x = f y) (q : f y = f z)
    : eq_of_fn_eq_fn' f (p @ q) = eq_of_fn_eq_fn' f p @ eq_of_fn_eq_fn' f q.
Proof.
    unfold eq_of_fn_eq_fn',
    refine _ @ (concat_pp_p _ _ _), apply whisker_right,
    refine _ @ (concat_pp_p _ _ _)^-1 @ (concat_pp_p _ _ _)^-1, apply whisker_left,
    refine (ap_pp _ _ _) @ _, apply whisker_left,
    refine !con_inv_cancel_left^-1
Defined.

Defined. equiv
