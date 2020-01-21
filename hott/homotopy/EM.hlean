(*
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Eilenberg MacLane spaces
*)

import hit.groupoid_quotient homotopy.hopf homotopy.freudenthal homotopy.homotopy_group
open algebra pointed nat eq category group is_trunc iso unit trunc equiv is_conn function is_equiv
     trunc_index

namespace EM
  open groupoid_quotient

  variables {G : Group}
Definition EM1' (G : Group) : Type.
  groupoid_quotient (Groupoid_of_Group G)
Definition EM1 (G : Group) : pType.
  pointed.MK (EM1' G) (elt star)

Definition base : EM1' G . elt star
Definition pth : G -> base = base . pth
Definition resp_mul (g h : G) : pth (g * h) = pth g @ pth h . resp_comp h g
Definition resp_one : pth (1 : G) = idp.
  resp_id star

Definition resp_inv (g : G) : pth (g^-1) = (pth g)^-1.
  resp_inv g

  local attribute pointed.MK pointed.carrier EM1 EM1' [reducible]
  protectedDefinition rec {P : EM1' G -> Type} [H : forall (x : EM1' G), is_trunc 1 (P x)]
    (Pb : P base) (Pp : forall (g : G), Pb =[pth g] Pb)
    (Pmul : forall (g h : G), change_path (resp_mul g h) (Pp (g * h)) = Pp g @o Pp h) (x : EM1' G) :
    P x.
Proof.
    induction x,
    { induction g, exact Pb},
    { induction a, induction b, exact Pp f},
    { induction a, induction b, induction c, exact Pmul f g}
Defined.

  protectedDefinition rec_on {P : EM1' G -> Type} [H : forall (x : EM1' G), is_trunc 1 (P x)]
    (x : EM1' G) (Pb : P base) (Pp : forall (g : G), Pb =[pth g] Pb)
    (Pmul : forall (g h : G), change_path (resp_mul g h) (Pp (g * h)) = Pp g @o Pp h) : P x.
  EM.rec Pb Pp Pmul x

  protectedDefinition set_rec {P : EM1' G -> Type} [H : forall (x : EM1' G), is_set (P x)]
    (Pb : P base) (Pp : forall (g : G), Pb =[pth g] Pb) (x : EM1' G) : P x.
  EM.rec Pb Pp !center x

  protectedDefinition prop_rec {P : EM1' G -> Type} [H : forall (x : EM1' G), is_prop (P x)]
    (Pb : P base) (x : EM1' G) : P x.
  EM.rec Pb !center !center x

Definition rec_pth {P : EM1' G -> Type} [H : forall (x : EM1' G), is_trunc 1 (P x)]
    {Pb : P base} {Pp : forall (g : G), Pb =[pth g] Pb}
    (Pmul : forall (g h : G), change_path (resp_mul g h) (Pp (g * h)) = Pp g @o Pp h)
    (g : G) : apd (EM.rec Pb Pp Pmul) (pth g) = Pp g.
  proof !rec_pth qed

  protectedDefinition elim {P : Type} [is_trunc 1 P] (Pb : P) (Pp : forall (g : G), Pb = Pb)
    (Pmul : forall (g h : G), Pp (g * h) = Pp g @ Pp h) (x : EM1' G) : P.
Proof.
    induction x,
    { exact Pb},
    { exact Pp f},
    { exact Pmul f g}
Defined.

  protectedDefinition elim_on {P : Type} [is_trunc 1 P] (x : EM1' G)
    (Pb : P) (Pp : G -> Pb = Pb) (Pmul : forall (g h : G), Pp (g * h) = Pp g @ Pp h) : P.
  EM.elim Pb Pp Pmul x

  protectedDefinition set_elim {P : Type} [is_set P] (Pb : P) (Pp : G -> Pb = Pb)
    (x : EM1' G) : P.
  EM.elim Pb Pp !center x

  protectedDefinition prop_elim {P : Type} [is_prop P] (Pb : P) (x : EM1' G) : P.
  EM.elim Pb !center !center x

Definition elim_pth {P : Type} [is_trunc 1 P] {Pb : P} {Pp : G -> Pb = Pb}
    (Pmul : forall (g h : G), Pp (g * h) = Pp g @ Pp h) (g : G) : ap (EM.elim Pb Pp Pmul) (pth g) = Pp g.
  proof !elim_pth qed

  protectedDefinition elim_set.{u} (Pb : Set.{u}) (Pp : forall (g : G), Pb <~> Pb)
    (Pmul : forall (g h : G) (x : Pb), Pp (g * h) x = Pp h (Pp g x)) (x : EM1' G) : Set.{u}.
  groupoid_quotient.elim_set (fun u => Pb) (fun u v => Pp) (fun u v w g h => proof Pmul h g qed) x

Definition elim_set_pth {Pb : Set} {Pp : forall (g : G), Pb <~> Pb}
    (Pmul : forall (g h : G) (x : Pb), Pp (g * h) x = Pp h (Pp g x)) (g : G) :
    transport (EM.elim_set Pb Pp Pmul) (pth g) = Pp g.
  !elim_set_pth

Defined. EM







namespace EM
  open groupoid_quotient

  variables (G : Group)
Definition base_eq_base_equiv : (base = base :> EM1 G) <~> G.
  !elt_eq_elt_equiv

Definition fundamental_group_EM1 : forall ₁ (EM1 G) <~>g G.
Proof.
    fapply isomorphism_of_equiv,
    { exact trunc_equiv_trunc 0 !base_eq_base_equiv @e trunc_equiv 0 G},
    { intros g h, induction g with p, induction h with q,
      exact encode_con p q}
Defined.

  proposition is_trunc_EM1 [instance] : is_trunc 1 (EM1 G).
  !is_trunc_groupoid_quotient

  proposition is_trunc_EM1' [instance] : is_trunc 1 (EM1' G).
  !is_trunc_groupoid_quotient

  proposition is_conn_EM1' [instance] : is_conn 0 (EM1' G).
  by apply @is_conn_groupoid_quotient; esimp; exact _

  proposition is_conn_EM1 [instance] : is_conn 0 (EM1 G).
  is_conn_EM1' G

  variable {G}
Definition EM1_map {X : pType} (e : G -> loops X)
    (r : forall g h, e (g * h) = e g @ e h) [is_conn 0 X] [is_trunc 1 X] : EM1 G -> X.
Proof.
    intro x, induction x using EM.elim,
    { exact Point X },
    { exact e g },
    { exact r g h }
Defined.

  (* Uniqueness of K(G, 1) *)

Definition EM1_pmap {X : pType} (e : G -> loops X)
    (r : forall g h, e (g * h) = e g @ e h) [is_conn 0 X] [is_trunc 1 X] : EM1 G ->* X.
  Build_pMap (EM1_map e r) idp

  variable (G)
Definition loop_EM1 : G <~>* loops (EM1 G).
  (pequiv_of_equiv (base_eq_base_equiv G) idp)^-1ᵉ*

  variable {G}
Definition loop_EM1_pmap {X : pType} (e : G ->* loops X)
    (r : forall g h, e (g * h) = e g @ e h) [is_conn 0 X] [is_trunc 1 X] :
    Ω->(EM1_pmap e r) o* loop_EM1 G ==* e.
Proof.
    fapply Build_pHomotopy,
    { intro g, refine (concat_1p _) @ elim_pth r g },
    { apply is_set.elim }
Defined.

Definition EM1_pequiv'.{u} {G : Group.{u}} {X : pType.{u}} (e : G <~>* loops X)
    (r : forall g h, e (g * h) = e g @ e h) [is_conn 0 X] [is_trunc 1 X] : EM1 G <~>* X.
Proof.
    apply pequiv_of_pmap (EM1_pmap e r),
    apply whitehead_principle_pointed 1,
    intro k, cases k with k,
    { apply @is_equiv_of_is_contr,
      all_goals (esimp; exact _)},
    { cases k with k,
      { apply is_equiv_trunc_functor => esimp,
        apply is_equiv.homotopy_closed, rotate 1,
        { symmetry, exact phomotopy_pinv_right_of_phomotopy (loop_EM1_pmap _ _) },
        apply is_equiv_compose e, apply pequiv.to_is_equiv },
      { apply @is_equiv_of_is_contr,
        do 2 exact trivial_homotopy_group_of_is_trunc _ (succ_lt_succ !zero_lt_succ)}}
Defined.

Definition EM1_pequiv.{u} {G : Group.{u}} {X : pType.{u}} (e : G <~>g forall ₁ X)
    [is_conn 0 X] [is_trunc 1 X] : EM1 G <~>* X.
Proof.
    apply EM1_pequiv' (pequiv_of_isomorphism e @e* ptrunc_pequiv 0 (loops X)),
    refine equiv.preserve_binary_of_inv_preserve _ mul concat _,
    intro p q,
    exact to_respect_mul e^-1ᵍ (tr p) (tr q)
Defined.

Definition EM1_pequiv_type (X : pType) [is_conn 0 X] [is_trunc 1 X] : EM1 (forall ₁ X) <~>* X.
  EM1_pequiv !isomorphism.refl

Defined. EM

open hopf susp
namespace EM
  (* EM1 G is an h-space if G is an abelian group. This allows us to construct K(G,n) for n ≥ 2 *)
  variables {G : AbGroup} (n : ℕ)

Definition EM1_mul [unfold 2 3] (x x' : EM1' G) : EM1' G.
Proof.
    induction x,
    { exact x'},
    { induction x' using EM.set_rec,
      { exact pth g},
      { exact abstract begin apply loop_pathover, apply square_of_eq,
          refine !resp_mul^-1 @ _ @ !resp_mul,
          exact ap pth !mul.comm end end}},
    { refine EM.prop_rec _ x', apply resp_mul }
Defined.

  variable (G)
Definition EM1_mul_one (x : EM1' G) : EM1_mul x base = x.
Proof.
    induction x using EM.set_rec,
    { reflexivity},
    { apply eq_pathover_id_right, apply hdeg_square, refine EM.elim_pth _ g}
Defined.

Definition h_space_EM1 [instance] : h_space (EM1' G).
Proof.
    fapply h_space.mk,
    { exact EM1_mul},
    { exact base},
    { intro x', reflexivity},
    { apply EM1_mul_one}
Defined.

  (* K(G, n+1) *)
Definition EMadd1 : ℕ -> pType
  | 0 . EM1 G
  | (n+1) . ptrunc (n+2) (susp (EMadd1 n))

Definition EMadd1_succ [unfold_full] (n : ℕ) :
    EMadd1 G (succ n) = ptrunc (n.+2) (susp (EMadd1 G n)).
  idp

Definition loop_EM2 : Ω[1] (EMadd1 G 1) <~>* EM1 G.
  hopf.delooping (EM1' G) idp

Definition is_conn_EMadd1 [instance] (n : ℕ) : is_conn n (EMadd1 G n).
Proof.
    induction n with n IH,
    { apply is_conn_EM1 },
    { rewrite EMadd1_succ, exact _ }
Defined.

Definition is_trunc_EMadd1 [instance] (n : ℕ) : is_trunc (n+1) (EMadd1 G n).
Proof.
    cases n with n,
    { apply is_trunc_EM1 },
    { apply is_trunc_trunc }
Defined.

  (* loops of an EM-space *)
Definition loop_EMadd1 (n : ℕ) : EMadd1 G n <~>* loops (EMadd1 G (succ n)) .
Proof.
    cases n with n,
    { exact !loop_EM2^-1ᵉ* },
    { rewrite [EMadd1_succ G (succ n)],
      refine (ptrunc_pequiv (succ n + 1) _)^-1ᵉ*  @e* _ @e* (loop_ptrunc_pequiv _ _)^-1ᵉ*,
      have succ n + 1 ≤ 2 * succ n, from add_mul_le_mul_add n 1 1,
      refine freudenthal_pequiv _ this }
Defined.

Definition loopn_EMadd1_pequiv_EM1 (G : AbGroup) (n : ℕ) : EM1 G <~>* Ω[n] (EMadd1 G n).
Proof.
    induction n with n e,
    { reflexivity },
    { refine _ @e* !loopn_succ_in^-1ᵉ*,
      refine _ @e* loopn_pequiv_loopn n !loop_EMadd1,
      exact e }
Defined.

  (* use loopn_EMadd1_pequiv_EM1 in thisDefinition? *)
Definition loopn_EMadd1 (G : AbGroup) (n : ℕ) : G <~>* Ω[succ n] (EMadd1 G n).
Proof.
    induction n with n e,
    { apply loop_EM1 },
    { refine _ @e* !loopn_succ_in^-1ᵉ*,
      refine _ @e* loopn_pequiv_loopn (succ n) !loop_EMadd1,
      exact e }
Defined.

Definition loopn_EMadd1_succ [unfold_full] (G : AbGroup) (n : ℕ) : loopn_EMadd1 G (succ n) ==*
    !loopn_succ_in^-1ᵉ* o* apn (succ n) !loop_EMadd1 o* loopn_EMadd1 G n.
  by reflexivity

Definition EM_up {G : AbGroup} {X : pType} {n : ℕ} (e : Ω[succ (succ n)] X <~>* G)
    : Ω[succ n] (loops X) <~>* G.
  !loopn_succ_in^-1ᵉ* @e* e

Definition is_homomorphism_EM_up {G : AbGroup} {X : pType} {n : ℕ}
    (e : Ω[succ (succ n)] X <~>* G)
    (r : forall (p q : Ω[succ (succ n)] X), e (p @ q) = e p * e q)
    (p q : Ω[succ n] (loops X)) : EM_up e (p @ q) = EM_up e p * EM_up e q.
Proof.
    refine _ @ !r, apply ap e, esimp, apply apn_con
Defined.

Definition EMadd1_pmap {G : AbGroup} {X : pType} (n : ℕ)
    (e : Ω[succ n] X <~>* G)
    (r : forall p q, e (p @ q) = e p * e q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n ->* X.
Proof.
    revert X e r H1 H2, induction n with n f: intro X e r H1 H2,
    { exact EM1_pmap e^-1ᵉ* (equiv.inv_preserve_binary e concat mul r) },
    rewrite [EMadd1_succ],
    exact ptrunc.elim ((succ n).+1)
            (susp_elim (f _ (EM_up e) (is_homomorphism_EM_up e r) _ _)),
Defined.

Definition EMadd1_pmap_succ {G : AbGroup} {X : pType} (n : ℕ) (e : Ω[succ (succ n)] X <~>* G)
    r [H1 : is_conn (succ n) X] [H2 : is_trunc ((succ n).+1) X] : EMadd1_pmap (succ n) e r =
    ptrunc.elim ((succ n).+1) (susp_elim (EMadd1_pmap n (EM_up e) (is_homomorphism_EM_up e r))).
  by reflexivity

Definition loop_EMadd1_pmap {G : AbGroup} {X : pType} {n : ℕ} (e : Ω[succ (succ n)] X <~>* G)
    (r : forall p q, e (p @ q) = e p * e q)
    [H1 : is_conn (succ n) X] [H2 : is_trunc ((succ n).+1) X] :
    Ω->(EMadd1_pmap (succ n) e r) o* loop_EMadd1 G n ==*
    EMadd1_pmap n (EM_up e) (is_homomorphism_EM_up e r).
Proof.
    cases n with n,
    { apply hopf_delooping_elim },
    { refine !passoc^-1* @* _,
      rewrite [EMadd1_pmap_succ (succ n)],
      refine pwhisker_right _ !ap1_ptrunc_elim @* _,
      refine !passoc^-1* @* _,
      refine pwhisker_right _ (ptrunc_elim_freudenthal_pequiv
                                (succ n) (succ (succ n)) (add_mul_le_mul_add n 1 1) _) @* _,
      reflexivity }
Defined.

Definition loopn_EMadd1_pmap' {G : AbGroup} {X : pType} {n : ℕ} (e : Ω[succ n] X <~>* G)
    (r : forall p q, e (p @ q) = e p * e q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] :
    Ω->[succ n](EMadd1_pmap n e r) o* loopn_EMadd1 G n ==* e^-1ᵉ*.
Proof.
    revert X e r H1 H2, induction n with n IH: intro X e r H1 H2,
    { apply loop_EM1_pmap },
    refine pwhisker_left _ !loopn_EMadd1_succ @* _,
    refine !passoc^-1* @* _,
    refine pwhisker_right _ !loopn_succ_in_inv_natural @* _,
    refine !passoc @* _,
    refine pwhisker_left _ (!passoc^-1* @*
             pwhisker_right _ (!apn_pcompose^-1* @* apn_phomotopy _ !loop_EMadd1_pmap) @*
             !IH @* !pinv_trans_pinv_left) @* _,
    apply pinv_pcompose_cancel_left
Defined.

Definition EMadd1_pequiv' {G : AbGroup} {X : pType} (n : ℕ) (e : Ω[succ n] X <~>* G)
    (r : forall (p q : Ω[succ n] X), e (p @ q) = e p * e q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n <~>* X.
Proof.
    apply pequiv_of_pmap (EMadd1_pmap n e r),
    have is_conn 0 (EMadd1 G n), from is_conn_of_le _ (zero_le_of_nat n),
    have is_trunc (n.+1) (EMadd1 G n), from !is_trunc_EMadd1,
    refine whitehead_principle_pointed (n.+1) _ _,
    intro k, apply @nat.lt_by_cases k (succ n): intro H,
    { apply @is_equiv_of_is_contr,
      do 2 exact trivial_homotopy_group_of_is_conn _ (le_of_lt_succ H)},
    { cases H, esimp, apply is_equiv_trunc_functor => esimp,
      apply is_equiv.homotopy_closed, rotate 1,
      { symmetry, exact phomotopy_pinv_right_of_phomotopy (loopn_EMadd1_pmap' _ _) },
      apply is_equiv_compose (e^-1ᵉ*), apply pequiv.to_is_equiv },
    { apply @is_equiv_of_is_contr,
      do 2 exact trivial_homotopy_group_of_is_trunc _ H}
Defined.

Definition EMadd1_pequiv {G : AbGroup} {X : pType} (n : ℕ) (e : forall g[n+1] X <~>g G)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n <~>* X.
Proof.
    have is_set (Ω[succ n] X), from !is_set_loopn,
    apply EMadd1_pequiv' n ((ptrunc_pequiv _ _)^-1ᵉ* @e* pequiv_of_isomorphism e),
    intro p q, esimp, exact to_respect_mul e (tr p) (tr q)
Defined.

Definition EMadd1_pequiv_succ {G : AbGroup} {X : pType} (n : ℕ) (e : forall ag[n+2] X <~>g G)
    [H1 : is_conn (n.+1) X] [H2 : is_trunc (n.+2) X] : EMadd1 G (succ n) <~>* X.
  EMadd1_pequiv (succ n) e

Definition ghomotopy_group_EMadd1 (n : ℕ) : forall g[n+1] (EMadd1 G n) <~>g G.
Proof.
    change forall ₁ (Ω[n] (EMadd1 G n)) <~>g G,
    refine homotopy_group_isomorphism_of_pequiv 0 (loopn_EMadd1_pequiv_EM1 G n)^-1ᵉ* @g _,
    apply fundamental_group_EM1 =>
Defined.

Definition EMadd1_pequiv_type (X : pType) (n : ℕ) [is_conn (n+1) X] [is_trunc (n+1+1) X]
    : EMadd1 (forall ag[n+2] X) (succ n) <~>* X.
  EMadd1_pequiv_succ n !isomorphism.refl

  (* K(G, n) *)
Definition EM (G : AbGroup) : ℕ -> pType
  | 0     . G
  | (k+1) . EMadd1 G k

  namespace ops
    abbreviation K . @EM
Defined. ops
  open ops

Definition homotopy_group_EM (n : ℕ) : forall [n] (EM G n) <~>* G.
Proof.
    cases n with n,
    { rexact ptrunc_pequiv 0 G },
    { exact pequiv_of_isomorphism (ghomotopy_group_EMadd1 G n)}
Defined.

Definition ghomotopy_group_EM (n : ℕ) : forall g[n+1] (EM G (n+1)) <~>g G.
  ghomotopy_group_EMadd1 G n

Definition is_conn_EM [instance] (n : ℕ) : is_conn (n.-1) (EM G n).
Proof.
    cases n with n,
    { apply is_conn_minus_one, apply tr, unfold [EM], exact 1},
    { apply is_conn_EMadd1}
Defined.

Definition is_conn_EM_succ [instance] (n : ℕ) : is_conn n (EM G (succ n)).
  is_conn_EM G (succ n)

Definition is_trunc_EM [instance] (n : ℕ) : is_trunc n (EM G n).
Proof.
    cases n with n,
    { unfold [EM], apply semigroup.is_set_carrier},
    { apply is_trunc_EMadd1}
Defined.

Definition loop_EM (n : ℕ) : loops (K G (succ n)) <~>* K G n.
Proof.
    cases n with n,
    { refine _ @e* pequiv_of_isomorphism (fundamental_group_EM1 G) =>
      symmetry, apply ptrunc_pequiv },
    { exact !loop_EMadd1^-1ᵉ* }
Defined.

  open circle int
Definition EM_pequiv_circle : K agℤ 1 <~>* S¹*.
  EM1_pequiv fundamental_group_of_circle^-1ᵍ

  (* Functorial action of Eilenberg-Maclane spaces *)

Definition EM1_functor {G H : Group} (φ : G ->g H) : EM1 G ->* EM1 H.
Proof.
    fapply Build_pMap,
    { intro g, induction g,
      { exact base },
      { exact pth (φ g) },
      { exact ap pth (to_respect_mul φ g h) @ resp_mul (φ g) (φ h) }},
    { reflexivity }
Defined.

Definition EMadd1_functor {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
    EMadd1 G n ->* EMadd1 H n.
Proof.
    induction n with n ψ,
    { exact EM1_functor φ } =>
    { apply ptrunc_functor => apply susp_functor => exact ψ }
Defined.

Definition EM_functor {G H : AbGroup} (φ : G ->g H) (n : ℕ) :
    K G n ->* K H n.
Proof.
    cases n with n,
    { exact pmap_of_homomorphism φ },
    { exact EMadd1_functor φ n }
Defined.

  (* Equivalence of Groups and pointed connected 1-truncated types *)

Definition ptruncconntype10_pequiv (X Y : 1-pType[0]) (e : forall ₁ X <~>g forall ₁ Y) : X <~>* Y.
  (EM1_pequiv !isomorphism.refl)^-1ᵉ* @e* EM1_pequiv e

Definition EM1_pequiv_ptruncconntype10 (X : 1-pType[0]) : EM1 (forall ₁ X) <~>* X.
  EM1_pequiv_type X

Definition Group_equiv_ptruncconntype10 : Group <~> 1-pType[0].
  equiv.MK (fun G => ptruncconntype.mk (EM1 G) _ (point _) !is_conn_EM1)
           (fun X => forall ₁ X)
           begin intro X, apply ptruncconntype_eq, esimp, exact EM1_pequiv_type X end
           begin intro G, apply eq_of_isomorphism, apply fundamental_group_EM1 end

  (* Equivalence of AbGroups and pointed n-connected (n+1)-truncated types (n ≥ 1) *)

  open trunc_index
Definition ptruncconntype_pequiv : forall (n : ℕ) (X Y : (n.+1)-pType[n])
    (e : forall g[n+1] X <~>g forall g[n+1] Y), X <~>* Y
  | 0 X Y e . ptruncconntype10_pequiv X Y e
  | (succ n) X Y e.
Proof.
    refine (EMadd1_pequiv_succ n _)^-1ᵉ* @e* EMadd1_pequiv_succ n !isomorphism.refl,
    exact e
Defined.

Definition EM1_pequiv_ptruncconntype (n : ℕ) (X : (n+1+1)-pType[n+1]) :
    EMadd1 (forall ag[n+2] X) (succ n) <~>* X.
  EMadd1_pequiv_type X n

Definition AbGroup_equiv_ptruncconntype' (n : ℕ) :
    AbGroup <~> (n + 1 + 1)-pType[n+1].
  equiv.MK
    (fun G => ptruncconntype.mk (EMadd1 G (n+1)) _ (point _) _)
    (fun X => forall ag[n+2] X)
    begin intro X, apply ptruncconntype_eq, apply EMadd1_pequiv_type end
    begin intro G, apply AbGroup_eq_of_isomorphism, exact ghomotopy_group_EMadd1 G (n+1) end

Definition AbGroup_equiv_ptruncconntype (n : ℕ) :
    AbGroup <~> (n.+2)-pType[n.+1].
  AbGroup_equiv_ptruncconntype' n

Defined. EM
