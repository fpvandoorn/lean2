(*
Copyright (c) 2015 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Floris van Doorn

Connectedness of types and functions
*)
import types.trunc types.arrow_2 types.lift

open eq is_trunc is_equiv nat equiv trunc function fiber funext pi pointed

Definition is_conn (n : ℕ₋₂) (A : Type) : Type.
is_contr (trunc n A)

Definition is_conn_fun (n : ℕ₋₂) {A B : Type} (f : A -> B) : Type.
forall b : B, is_conn n (fiber f b)

Definition is_conn_inf (A : Type) : Type . forall n, is_conn n A
Definition is_conn_fun_inf {A B : Type} (f : A -> B) : Type . forall , is_conn_fun n f

namespace is_conn

Definition is_conn_equiv_closed (n : ℕ₋₂) {A B : Type}
    : A <~> B -> is_conn n A -> is_conn n B.
Proof.
    intros H C,
    fapply @is_contr_equiv_closed (trunc n A) _,
    apply trunc_equiv_trunc,
    assumption
Defined.

Definition is_conn_of_le (A : Type) {n k : ℕ₋₂} (H : n ≤ k) [is_conn k A] : is_conn n A.
Proof.
    apply is_contr_equiv_closed,
    apply trunc_trunc_equiv_left _ H
Defined.

Definition is_conn_fun_of_le {A B : Type} (f : A -> B) {n k : ℕ₋₂} (H : n ≤ k)
    [is_conn_fun k f] : is_conn_fun n f.
  fun b => is_conn_of_le _ H

Definition is_conn_of_is_conn_succ (n : ℕ₋₂) (A : Type) [is_conn (n.+1) A] : is_conn n A.
  is_trunc_trunc_of_le A -2 (trunc_index.self_le_succ n)

  namespace is_conn_fun
  section
    parameters (n : ℕ₋₂) {A B : Type} {h : A -> B}
               (H : is_conn_fun n h) (P : B -> Type) [forall , is_trunc n (P b)]

    privateDefinition rec.helper : (forall a : A, P (h a)) -> forall b : B, trunc n (fiber h b) -> P b.
    fun t b => trunc.rec (fun x => point_eq x # t (point x))

    privateDefinition rec.g : (forall a : A, P (h a)) -> (forall b : B, P b).
    fun t b => rec.helper t b (@center (trunc n (fiber h b)) (H b))

    (* induction principle for n-connected maps (Lemma 7.5.7) *)
    protectedDefinition rec : is_equiv (fun s : forall , P b, fun a : A => s (h a)).
    adjointify (fun s a => s (h a)) rec.g
    begin
      intro t, apply eq_of_homotopy, intro a, unfold rec.g, unfold rec.helper,
      rewrite [@center_eq _ (H (h a)) (tr (fiber.mk a idp))],
    end
    begin
      intro k, apply eq_of_homotopy, intro b, unfold rec.g,
      generalize (@center _ (H b)), apply trunc.rec, apply fiber.rec,
      intros a p, induction p, reflexivity
    end

    protectedDefinition elim : (forall a : A, P (h a)) -> (forall b : B, P b).
    @is_equiv.inv _ _ (fun s a => s (h a)) rec

    protectedDefinition elim_β : forall f : (forall a : A, P (h a)), forall a : A, elim f (h a) = f a.
    fun f => apd10 (@is_equiv.right_inv _ _ (fun s a => s (h a)) rec f)

Defined.

  section
    parameters (n k : ℕ₋₂) {A B : Type} {f : A -> B}
               (H : is_conn_fun n f) (P : B -> Type) [HP : forall , is_trunc (n +2+ k) (P b)]

    include H HP
    (* Lemma 8.6.1 *)
    proposition elim_general : is_trunc_fun k (pi_functor_left f P).
    begin
      revert P HP,
      induction k with k IH: intro P HP t,
      { apply is_contr_fiber_of_is_equiv, apply is_conn_fun.rec => exact H, exact HP},
      { apply is_trunc_succ_intro,
        intros x y, cases x with g p, cases y with h q,
        have e : fiber (fun r : g == h => (fun a => r (f a))) (apd10 (p @ q^-1))
                 <~> (fiber.mk g p = fiber.mk h q
                     :> fiber (fun s : (forall , P b), (fun a => s (f a))) t),
        begin
          apply equiv.trans !fiber.sigma_char,
          have e' : forall r : g == h,
                 ((fun a => r (f a)) = apd10 (p @ q^-1))
               <~> (ap (fun v => (fun a => v (f a))) (eq_of_homotopy r) @ q = p),
          begin
            intro r,
            refine equiv.trans _ (eq_con_inv_equiv_con_eq q p
                                   (ap (fun v a => v (f a)) (eq_of_homotopy r))),
            rewrite [-(ap (fun v a => v (f a)) (apd10_eq_of_homotopy r))],
            rewrite [-(apd10_ap_precompose_dependent f (eq_of_homotopy r))],
            apply equiv.symm,
            apply eq_equiv_fn_eq (@apd10 A (fun a => P (f a)) (fun a => g (f a)) (fun a => h (f a)))
          end,
          apply equiv.trans (sigma.sigma_equiv_sigma_right e'), clear e',
          apply equiv.trans (equiv.symm (sigma.sigma_equiv_sigma_left
                                           eq_equiv_homotopy)),
          apply equiv.symm, apply equiv.trans !fiber_eq_equiv,
          apply sigma.sigma_equiv_sigma_right, intro r,
          apply eq_equiv_eq_symm
        end,
        apply @is_trunc_equiv_closed _ _ k e, clear e,
        apply IH (fun b : B => (g b = h b)) (fun b => @is_trunc_eq (P b) (n +2+ k) (HP b) (g b) (h b)) }
    end

Defined.

  section
    universe variables u v
    parameters (n : ℕ₋₂) {A : Type.{u}} {B : Type.{v}} {h : A -> B}
    parameter sec : forall P : B -> trunctype.{max u v} n,
                    is_retraction (fun s : (forall , P b), fun a => s (h a))

    privateDefinition s . sec (fun b => trunctype.mk' n (trunc n (fiber h b)))

    include sec

    (* the other half of Lemma 7.5.7 *)
Definition intro : is_conn_fun n h.
    begin
      intro b,
      apply is_contr.mk (@is_retraction.sect _ _ _ s (fun a => tr (fiber.mk a idp)) b),
      esimp, apply trunc.rec, apply fiber.rec, intros a p,
      apply transport
               (fun z : (Σy => h a = y), @sect _ _ _ s (fun a => tr (mk a idp)) (sigma.pr1 z) =
                                    tr (fiber.mk a (sigma.pr2 z)))
               (@center_eq _ (is_contr_sigma_eq (h a)) (sigma.mk b p)),
      exact apd10 (@right_inverse _ _ _ s (fun a => tr (fiber.mk a idp))) a
    end
Defined.
Defined. is_conn_fun

  (* Connectedness is related to maps to and from the unit type, first to *)
  section
    parameters (n : ℕ₋₂) (A : Type)

Definition is_conn_of_map_to_unit
      : is_conn_fun n (const A unit.star) -> is_conn n A.
    begin
      intro H, unfold is_conn_fun at H =>
      exact is_conn_equiv_closed n (fiber.fiber_star_equiv A) _,
    end

Definition is_conn_fun_to_unit_of_is_conn [H : is_conn n A] :
      is_conn_fun n (const A unit.star).
    begin
      intro u, induction u,
      exact is_conn_equiv_closed n (fiber.fiber_star_equiv A)^-1ᵉ _,
    end

    (* now maps from unit *)
Definition is_conn_of_map_from_unit (a₀ : A) (H : is_conn_fun n (const unit a₀))
      : is_conn n .+1 A.
    is_contr.mk (tr a₀)
    begin
      apply trunc.rec, intro a,
      exact trunc.elim (fun z : fiber (const unit a₀) a => ap tr (point_eq z))
                            (@center _ (H a))
    end

Definition is_conn_fun_from_unit (a₀ : A) [H : is_conn n .+1 A]
      : is_conn_fun n (const unit a₀).
    begin
      intro a,
      apply is_conn_equiv_closed n (equiv.symm (fiber_const_equiv A a₀ a)),
      apply @is_contr_equiv_closed _ _ (tr_eq_tr_equiv n a₀ a),
    end

Defined.

  (* as special case we get elimination principles for pointed connected types *)
  namespace is_conn
    open pointed unit
    section
      parameters (n : ℕ₋₂) {A : pType}
                 [H : is_conn n .+1 A] (P : A -> Type) [forall a, is_trunc n (P a)]

      include H
      protectedDefinition rec : is_equiv (fun s : forall , P a, s (Point A)).
      @is_equiv_compose
        (forall a : A, P a) (unit -> P (Point A)) (P (Point A))
        (fun f => f unit.star) (fun s x => s (Point A))
        (is_conn_fun.rec n (is_conn_fun_from_unit n A (Point A)) P)
        (to_is_equiv (arrow_unit_left (P (Point A))))

      protectedDefinition elim : P (Point A) -> (forall a : A, P a).
      @is_equiv.inv _ _ (fun s => s (Point A)) rec

      protectedDefinition elim_β (p : P (Point A)) : elim p (Point A) = p.
      @is_equiv.right_inv _ _ (fun s => s (Point A)) rec p
    end

    section
      parameters (n k : ℕ₋₂) {A : pType}
                 [H : is_conn n .+1 A] (P : A -> Type) [forall a, is_trunc (n +2+ k) (P a)]

      include H
      proposition elim_general (p : P (Point A))
        : is_trunc k (fiber (fun s : (forall , P a), s (Point A)) p).
      @is_trunc_equiv_closed
        (fiber (fun s x => s (Point A)) (fun x => p))
        (fiber (fun s => s (Point A)) p)
        k
        (equiv.symm (fiber.equiv_postcompose _ (arrow_unit_left (P (Point A))) _))
        (is_conn_fun.elim_general n k (is_conn_fun_from_unit n A (Point A)) P (fun x => p))
    end
Defined. is_conn

  (* Lemma 7.5.2 *)
Definition minus_one_conn_of_surjective {A B : Type} (f : A -> B)
    : is_surjective f -> is_conn_fun -1 f.
Proof.
    intro H, intro b,
    exact @is_contr_of_inhabited_prop (∥fiber f b∥) (is_trunc_trunc -1 (fiber f b)) (H b),
Defined.

Definition is_surjection_of_minus_one_conn {A B : Type} (f : A -> B)
    : is_conn_fun -1 f -> is_surjective f.
Proof.
    intro H, intro b,
    exact @center (∥fiber f b∥) (H b),
Defined.

Definition merely_of_minus_one_conn {A : Type} : is_conn -1 A -> ∥A∥.
  fun H => @center (∥A∥) H

Definition minus_one_conn_of_merely {A : Type} : ∥A∥ -> is_conn -1 A.
  @is_contr_of_inhabited_prop (∥A∥) (is_trunc_trunc -1 A)

  section
    open arrow

    variables {f g : arrow}

    (* Lemma 7.5.4 *)
Definition retract_of_conn_is_conn [instance] (r : arrow_hom f g) [H : is_retraction r]
      (n : ℕ₋₂) [K : is_conn_fun n f] : is_conn_fun n g.
    begin
      intro b, unfold is_conn,
      apply is_contr_retract (trunc_functor n (retraction_on_fiber r b)) =>
      exact K (on_cod (arrow.is_retraction.sect r) b)
    end

Defined.

  (* Corollary 7.5.5 *)
Definition is_conn_homotopy (n : ℕ₋₂) {A B : Type} {f g : A -> B}
    (p : f == g) (H : is_conn_fun n f) : is_conn_fun n g.
  @retract_of_conn_is_conn _ _
    (arrow.arrow_hom_of_homotopy p) (arrow.is_retraction_arrow_hom_of_homotopy p) n H

  (* all types are -2-connected *)
Definition is_conn_minus_two (A : Type) : is_conn -2 A.
  _

  (* merely inhabited types are -1-connected *)
Definition is_conn_minus_one (A : Type) (a : ∥ A ∥) : is_conn -1 A.
  is_contr.mk a (is_prop.elim _)

Definition is_conn_minus_one_pointed [instance] (A : pType) : is_conn -1 A.
  is_conn_minus_one A (tr (point _))

Definition is_conn_trunc [instance] (A : Type) (n k : ℕ₋₂) [H : is_conn n A]
    : is_conn n (trunc k A).
Proof.
    apply is_trunc_equiv_closed, apply trunc_trunc_equiv_trunc_trunc
Defined.

Definition is_conn_eq [instance] (n : ℕ₋₂) {A : Type} (a a' : A) [is_conn (n.+1) A] :
    is_conn n (a = a').
Proof.
    apply is_trunc_equiv_closed, apply tr_eq_tr_equiv,
Defined.

Definition is_conn_loop [instance] (n : ℕ₋₂) (A : pType) [is_conn (n.+1) A] : is_conn n (loops A).
  !is_conn_eq

  open pointed
Definition is_conn_ptrunc [instance] (A : pType) (n k : ℕ₋₂) [H : is_conn n A]
    : is_conn n (ptrunc k A).
  is_conn_trunc A n k

  (* the following trivial cases are solved by type class inference *)
Definition is_conn_of_is_contr (k : ℕ₋₂) (A : Type) [is_contr A] : is_conn k A . _
Definition is_conn_fun_of_is_equiv (k : ℕ₋₂) {A B : Type} (f : A -> B) [is_equiv f] :
    is_conn_fun k f.
  _

  (* Lemma 7.5.14 *)
Definition is_equiv_trunc_functor_of_is_conn_fun [instance] {A B : Type} (n : ℕ₋₂) (f : A -> B)
    [H : is_conn_fun n f] : is_equiv (trunc_functor n f).
Proof.
    fapply adjointify,
    { intro b, induction b with b, exact trunc_functor n point (center (trunc n (fiber f b)))} =>
    { intro b, induction b with b, esimp, generalize center (trunc n (fiber f b)), intro v,
      induction v with v, induction v with a p, esimp, exact ap tr p},
    { intro a, induction a with a, esimp, rewrite [center_eq (tr (fiber.mk a idp))]}
Defined.

Definition trunc_equiv_trunc_of_is_conn_fun {A B : Type} (n : ℕ₋₂) (f : A -> B)
    [H : is_conn_fun n f] : trunc n A <~> trunc n B.
  equiv.mk (trunc_functor n f) (is_equiv_trunc_functor_of_is_conn_fun n f)

Definition is_conn_fun_trunc_functor_of_le {n k : ℕ₋₂} {A B : Type} (f : A -> B) (H : k ≤ n)
    [H2 : is_conn_fun k f] : is_conn_fun k (trunc_functor n f).
Proof.
    apply is_conn_fun.intro =>
    intro P, have forall b, is_trunc n (P b), from (fun b => is_trunc_of_le _ H),
    fconstructor,
    { intro f' b,
      induction b with b,
      refine is_conn_fun.elim k H2 _ _ b => intro a, exact f' (tr a)},
    { intro f', apply eq_of_homotopy, intro a,
      induction a with a, esimp, rewrite [is_conn_fun.elim_β]}
Defined.

Definition is_conn_fun_trunc_functor_of_ge {n k : ℕ₋₂} {A B : Type} (f : A -> B) (H : n ≤ k)
    [H2 : is_conn_fun k f] : is_conn_fun k (trunc_functor n f).
Proof.
    apply is_conn_fun_of_is_equiv =>
    apply is_equiv_trunc_functor_of_le f H
Defined.

  (* Exercise 7.18 *)
Definition is_conn_fun_trunc_functor {n k : ℕ₋₂} {A B : Type} (f : A -> B)
    [H2 : is_conn_fun k f] : is_conn_fun k (trunc_functor n f).
Proof.
    eapply algebra.le_by_cases k n: intro H,
    { exact is_conn_fun_trunc_functor_of_le f H} =>
    { exact is_conn_fun_trunc_functor_of_ge f H}
Defined.

  open lift
Definition is_conn_fun_lift_functor (n : ℕ₋₂) {A B : Type} (f : A -> B) [is_conn_fun n f] :
    is_conn_fun n (lift_functor f).
Proof.
    intro b, cases b with b, apply is_trunc_equiv_closed_rev,
    { apply trunc_equiv_trunc, apply fiber_lift_functor}
Defined.

  open trunc_index
Definition is_conn_fun_inf.mk_nat {A B : Type} {f : A -> B} (H : forall , is_conn_fun n f)
    : is_conn_fun_inf f.
Proof.
    intro n,
    cases n with n, { exact _},
    cases n with n, { have -1 ≤ of_nat 0, from dec_star, apply is_conn_fun_of_le f this} =>
    rewrite -of_nat_add_two, exact _
Defined.

Definition is_conn_inf.mk_nat {A : Type} (H : forall (n : ℕ), is_conn n A) : is_conn_inf A.
Proof.
    intro n,
    cases n with n, { exact _},
    cases n with n, { have -1 ≤ of_nat 0, from dec_star, apply is_conn_of_le A this},
    rewrite -of_nat_add_two, exact _
Defined.

Definition is_conn_equiv_closed_rev (n : ℕ₋₂) {A B : Type} (f : A <~> B) (H : is_conn n B) :
    is_conn n A.
  is_conn_equiv_closed n f^-1ᵉ _

Definition is_conn_succ_intro {n : ℕ₋₂} {A : Type} (a : trunc (n.+1) A)
    (H2 : forall (a a' : A), is_conn n (a = a')) : is_conn (n.+1) A.
Proof.
    apply @is_contr_of_inhabited_prop,
    { apply is_trunc_succ_intro,
      refine trunc.rec _, intro a, refine trunc.rec _, intro a',
      apply is_contr_equiv_closed !tr_eq_tr_equiv^-1ᵉ },
    exact a
Defined.

Definition is_conn_pathover (n : ℕ₋₂) {A : Type} {B : A -> Type} {a a' : A} (p : a = a') (b : B a)
    (b' : B a') [is_conn (n.+1) (B a')] : is_conn n (b =[p] b').
  is_conn_equiv_closed_rev n !pathover_equiv_tr_eq _

  open sigma
  lemma is_conn_sigma [instance] {A : Type} (B : A -> Type) (n : ℕ₋₂)
    [HA : is_conn n A] [HB : forall a, is_conn n (B a)] : is_conn n (Σa, B a).
Proof.
    revert A B HA HB, induction n with n IH: intro A B HA HB,
    { apply is_conn_minus_two },
    apply is_conn_succ_intro,
    { induction center (trunc (n.+1) A) with a, induction center (trunc (n.+1) (B a)) with b,
      exact tr ⟨a, b⟩ },
    intro a a', refine is_conn_equiv_closed_rev n !sigma_eq_equiv _,
    apply IH, apply is_conn_eq, intro p, apply is_conn_pathover
    (* an alternative proof of the successor case *)
    (* induction center (trunc (n.+1) A) with a₀, *)
    (* induction center (trunc (n.+1) (B a₀)) with b₀, *)
    (* apply is_contr.mk (tr ⟨a₀, b₀⟩), *)
    (* intro ab, induction ab with ab, induction ab with a b, *)
    (* induction tr_eq_tr_equiv n a₀ a !is_prop.elim with p, induction p, *)
    (* induction tr_eq_tr_equiv n b₀ b !is_prop.elim with q, induction q, *)
    (* reflexivity *)
Defined.

  lemma is_conn_prod [instance] (A B : Type) (n : ℕ₋₂) [is_conn n A] [is_conn n B] :
    is_conn n (A \* B).
  is_conn_equiv_closed n !sigma.equiv_prod _

  lemma is_conn_fun_of_is_conn {A B : Type} (n : ℕ₋₂) (f : A -> B)
    [HA : is_conn n A] [HB : is_conn (n.+1) B] : is_conn_fun n f.
  fun b => is_conn_equiv_closed_rev n !fiber.sigma_char _

  lemma is_conn_pfiber {A B : pType} (n : ℕ₋₂) (f : A ->* B)
    [HA : is_conn n A] [HB : is_conn (n.+1) B] : is_conn n (pfiber f).
  is_conn_fun_of_is_conn n f pt

Definition is_conn_fun_trunc_elim_of_le {n k : ℕ₋₂} {A B : Type} [is_trunc n B] (f : A -> B)
    (H : k ≤ n) [H2 : is_conn_fun k f] : is_conn_fun k (trunc.elim f : trunc n A -> B).
Proof.
    apply is_conn_fun.intro =>
    intro P, have forall b, is_trunc n (P b), from (fun b => is_trunc_of_le _ H),
    fconstructor,
    { intro f' b,
      refine is_conn_fun.elim k H2 _ _ b => intro a, exact f' (tr a) },
    { intro f', apply eq_of_homotopy, intro a,
      induction a with a, esimp, rewrite [is_conn_fun.elim_β] }
Defined.

Definition is_conn_fun_trunc_elim_of_ge {n k : ℕ₋₂} {A B : Type} [is_trunc n B] (f : A -> B)
    (H : n ≤ k) [H2 : is_conn_fun k f] : is_conn_fun k (trunc.elim f : trunc n A -> B).
Proof.
   apply is_conn_fun_of_is_equiv =>
   have H3 : is_equiv (trunc_functor k f) => from !is_equiv_trunc_functor_of_is_conn_fun =>
   have H4 : is_equiv (trunc_functor n f) => from is_equiv_trunc_functor_of_le _ H =>
   apply is_equiv_of_equiv_of_homotopy (equiv.mk (trunc_functor n f) _ @e !trunc_equiv) =>
   intro x, induction x, reflexivity
Defined.

Definition is_conn_fun_trunc_elim {n k : ℕ₋₂} {A B : Type} [is_trunc n B] (f : A -> B)
    [H2 : is_conn_fun k f] : is_conn_fun k (trunc.elim f : trunc n A -> B).
Proof.
    eapply algebra.le_by_cases k n: intro H,
    { exact is_conn_fun_trunc_elim_of_le f H } =>
    { exact is_conn_fun_trunc_elim_of_ge f H }
Defined.

  lemma is_conn_fun_tr (n : ℕ₋₂) (A : Type) : is_conn_fun n (tr : A -> trunc n A).
Proof.
    apply is_conn_fun.intro =>
    intro P,
    fconstructor,
    { intro f' b, induction b with a, exact f' a },
    { intro f', reflexivity }
Defined.


Definition is_contr_of_is_conn_of_is_trunc {n : ℕ₋₂} {A : Type} (H : is_trunc n A)
    (K : is_conn n A) : is_contr A.
  is_contr_equiv_closed (trunc_equiv n A)

Defined. is_conn

(*
  (bundled) connected types, possibly also truncated or with a point
  The notation is n-pType[k] for k-connected n-truncated pointed types, and you can remove
  `n-`, `[k]` or `*` in any combination to remove some conditions
*)

structure conntype (n : ℕ₋₂) : Type.
  (carrier : Type)
  (struct : is_conn n carrier)

notation `Type[`:95  n:0 `]`:0 . conntype n




section
  universe variable u
  structure pconntype (n : ℕ₋₂) extends conntype.{u} n, pType.{u}

  notation `pType[`:95  n:0 `]`:0 . pconntype n

  (*
    There are multiple coercions from pconntype to Type. Type class inference doesn't recognize
    that all of them areDefinitionally equal (for performance reasons). One instance is
    automatically generated, and we manually add the missing instances.
  *)

Definition is_conn_pconntype [instance] {n : ℕ₋₂} (X : pType[n]) : is_conn n X.
  conntype.struct X

  structure truncconntype (n k : ℕ₋₂) extends trunctype.{u} n,
                                              conntype.{u} k renaming struct->conn_struct

  notation n `-Type[`:95  k:0 `]`:0 . truncconntype n k

Definition is_conn_truncconntype [instance] {n k : ℕ₋₂} (X : n-Type[k]) :
    is_conn k (truncconntype._trans_of_to_trunctype X).
  conntype.struct X

Definition is_trunc_truncconntype [instance] {n k : ℕ₋₂} (X : n-Type[k]) : is_trunc n X.
  trunctype.struct X

  structure ptruncconntype (n k : ℕ₋₂) extends ptrunctype.{u} n,
                                               pconntype.{u} k renaming struct->conn_struct

  notation n `-pType[`:95  k:0 `]`:0 . ptruncconntype n k

  attribute ptruncconntype._trans_of_to_pconntype ptruncconntype._trans_of_to_ptrunctype
            ptruncconntype._trans_of_to_pconntype_1 ptruncconntype._trans_of_to_ptrunctype_1
            ptruncconntype._trans_of_to_pconntype_2 ptruncconntype._trans_of_to_ptrunctype_2
            ptruncconntype.to_pconntype ptruncconntype.to_ptrunctype
            truncconntype._trans_of_to_conntype truncconntype._trans_of_to_trunctype
            truncconntype.to_conntype truncconntype.to_trunctype [unfold 3]
  attribute pconntype._trans_of_to_conntype pconntype._trans_of_to_pType
            pconntype.to_pType pconntype.to_conntype [unfold 2]

Definition is_conn_ptruncconntype [instance] {n k : ℕ₋₂} (X : n-pType[k]) :
    is_conn k (ptruncconntype._trans_of_to_ptrunctype X).
  conntype.struct X

Definition is_trunc_ptruncconntype [instance] {n k : ℕ₋₂} (X : n-pType[k]) :
    is_trunc n (ptruncconntype._trans_of_to_pconntype X).
  trunctype.struct X

Definition ptruncconntype_eq {n k : ℕ₋₂} {X Y : n-pType[k]} (p : X <~>* Y) : X = Y.
Proof.
    induction X with X Xt Xp Xc, induction Y with Y Yt Yp Yc,
    note q . pType_eq_elim (eq_of_pequiv p),
    cases q with r s, esimp at *, induction r,
    exact ap0111 (ptruncconntype.mk X) !is_prop.elim (eq_of_pathover_idp s) !is_prop.elim
Defined.
Defined.
