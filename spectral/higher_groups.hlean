(*
Copyright (c) 2015 Ulrik Buchholtz, Egbert Rijke and Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke, Floris van Doorn

Formalization of the higher groups paper
*)

import .homotopy.EM algebra.category.constructions.pullback
open eq is_conn pointed is_trunc trunc equiv is_equiv trunc_index susp nat algebra
  prod.ops sigma sigma.ops category EM
namespace higher_group
set_option pp.binder_types true
universe variable u

(* Results not necessarily about higher groups which we repeat here, because they are mentioned in
  the higher group paper *)
namespace hide
open pushout
Definition connect_intro_pequiv {k : ℕ} {B : pType} (A : pType) (H : is_conn k B) :
  ppMap B (connect k A) <~>* ppMap B A.
is_conn.connect_intro_pequiv A H

Definition is_conn_fun_prod_of_wedge (n m : ℕ) (A B : pType)
  [cA : is_conn n A] [cB : is_conn m B] : is_conn_fun (m + n) (@prod_of_wedge A B).
is_conn_fun_prod_of_wedge n m A B

Definition is_trunc_ppi_of_is_conn (k n : ℕ) (X : pType) (H : is_conn (k.-1) X)
  (Y : X -> pType) (H3 : forall x, is_trunc (k + n) (Y x)) :
  is_trunc n (ppforall (x : X), Y x).
is_conn.is_trunc_ppi_of_is_conn _ (k.-2) H _ _ (le_of_eq (sub_one_add_plus_two_sub_one k n)^-1) _ H3

Defined. hide

(* The k-groupal n-types.
  We require that the carrier has a point (preserved by the equivalence) *)

structure GType (n k : ℕ) : Type . (* (n,k)GType, denoted here as [n;k]GType *)
  (car : ptrunctype.{u} n)
  (B : pconntype.{u} (k.-1)) (* this is Bᵏ *)
  (e : car <~>* Ω[k] B)

structure InfGType (k : ℕ) : Type . (* (∞,k)GType, denoted here as [∞;k]GType *)
  (car : pType.{u})
  (B : pconntype.{u} (k.-1)) (* this is Bᵏ *)
  (e : car <~>* Ω[k] B)

structure ωGType (n : ℕ) . (* (n,ω)GType, denoted here as [n;ω]GType *)
  (B : forall (k : ℕ), (n+k)-pType[k.-1])
  (e : forall (k : ℕ), B k <~>* loops (B (k+1)))



variables {n k k' l : ℕ}
notation `[`:95 n:0 `; ` k `]GType`:0 . GType n k
notation `[∞; `:95 k:0 `]GType`:0 . InfGType k
notation `[`:95 n:0 `;ω]GType`:0 . ωGType n

open GType
open InfGType (renaming B->iB e->ie)
open ωGType (renaming B->oB e->oe)

(* some basic properties *)
lemma is_trunc_B' (G : [n;k]GType) : is_trunc (k+n) (B G).
Proof.
  apply is_trunc_of_is_trunc_loopn,
  exact is_trunc_equiv_closed _ (e G) _,
  exact _
Defined.

lemma is_trunc_B (G : [n;k]GType) : is_trunc (n+k) (B G).
transport (fun m => is_trunc m (B G)) (add.comm k n) (is_trunc_B' G)

local attribute [instance] is_trunc_B

Definition GType.sigma_char (n k : ℕ) :
  GType.{u} n k <~> Σ(B : pconntype.{u} (k.-1)), Σ(X : ptrunctype.{u} n), X <~>* Ω[k] B.
Proof.
  fapply equiv.MK,
  { intro G, exact ⟨B G, G, e G⟩ },
  { intro v, exact GType.mk v.2.1 v.1 v.2.2 },
  { intro v, induction v with v₁ v₂, induction v₂, reflexivity },
  { intro G, induction G, reflexivity },
Defined.

Definition GType_equiv (n k : ℕ) : [n;k]GType <~> (n+k)-pType[k.-1].
GType.sigma_char n k @e
sigma_equiv_of_is_embedding_left_contr
  ptruncconntype.to_pconntype
  (is_embedding_ptruncconntype_to_pconntype (n+k) (k.-1))
Proof.
  intro X,
  apply is_trunc_equiv_closed_rev -2,
  { apply sigma_equiv_sigma_right, intro B',
  refine _ @e (ptrunctype_eq_equiv B' (ptrunctype.mk (Ω[k] X) !is_trunc_loopn_nat (point _)))^-1ᵉ,
  assert lem : forall (A : n-pType) (B : pType) (H : is_trunc n B),
  (A <~>* B) <~> (A <~>* (ptrunctype.mk B H (point _))),
  { intro A B'' H, induction B'', reflexivity },
  apply lem },
  exact _
Defined.
Proof.
  intro B' H, apply fiber.mk (ptruncconntype.mk B' (is_trunc_B (GType.mk H.1 B' H.2)) (point _) _),
  induction B' with G' B' e', reflexivity
Defined.

Definition GType_equiv_pequiv {n k : ℕ} (G : [n;k]GType) : GType_equiv n k G <~>* B G.
by reflexivity

Definition GType_eq_equiv {n k : ℕ} (G H : [n;k]GType) : (G = H :> [n;k]GType) <~> (B G <~>* B H).
eq_equiv_fn_eq (GType_equiv n k) _ _ @e !ptruncconntype_eq_equiv

Definition GType_eq {n k : ℕ} {G H : [n;k]GType} (e : B G <~>* B H) : G = H.
(GType_eq_equiv G H)^-1ᵉ e

(* similar properties for [∞;k]GType *)

Definition InfGType.sigma_char (k : ℕ) :
  InfGType.{u} k <~> Σ(B : pconntype.{u} (k.-1)), Σ(X : pType.{u}), X <~>* Ω[k] B.
Proof.
  fapply equiv.MK,
  { intro G, exact ⟨iB G, G, ie G⟩ },
  { intro v, exact InfGType.mk v.2.1 v.1 v.2.2 },
  { intro v, induction v with v₁ v₂, induction v₂, reflexivity },
  { intro G, induction G, reflexivity },
Defined.

Definition InfGType_equiv (k : ℕ) : [∞;k]GType <~> pType[k.-1].
InfGType.sigma_char k @e
@sigma_equiv_of_is_contr_right _ _
  (fun X => is_trunc_equiv_closed_rev -2 (sigma_equiv_sigma_right (fun B' => !pType_eq_equiv^-1ᵉ)) _)

Definition InfGType_equiv_pequiv {k : ℕ} (G : [∞;k]GType) : InfGType_equiv k G <~>* iB G.
by reflexivity

Definition InfGType_eq_equiv {k : ℕ} (G H : [∞;k]GType) : (G = H :> [∞;k]GType) <~> (iB G <~>* iB H).
eq_equiv_fn_eq (InfGType_equiv k) _ _ @e !pconntype_eq_equiv

Definition InfGType_eq {k : ℕ} {G H : [∞;k]GType} (e : iB G <~>* iB H) : G = H.
(InfGType_eq_equiv G H)^-1ᵉ e

(* alternative constructor for ωGType *)

Definition ωGType.mk_le {n : ℕ} (k₀ : ℕ)
  (C : forall (k : ℕ), k₀ ≤ k -> ((n+k)-pType[k.-1] : Type.{u+1}))
  (e : forall (k : ℕ) (H : k₀ ≤ k), C H <~>* loops (C (le.step H))) : ([n;ω]GType : Type.{u+1}).
Proof.
  fconstructor,
  { apply rec_down_le _ k₀ C, intro n' D,
  refine (ptruncconntype.mk (loops D) _ (point _) _),
  apply is_trunc_loop, apply is_trunc_ptruncconntype, apply is_conn_loop,
  apply is_conn_ptruncconntype },
  { intro n', apply rec_down_le_univ, exact e, intro n D, reflexivity }
Defined.

Definition ωGType.mk_le_beta {n : ℕ} {k₀ : ℕ}
  (C : forall (k : ℕ), k₀ ≤ k -> ((n+k)-pType[k.-1] : Type.{u+1}))
  (e : forall (k : ℕ) (H : k₀ ≤ k), C H <~>* loops (C (le.step H)))
  (k : ℕ) (H : k₀ ≤ k) : oB (ωGType.mk_le k₀ C e) k <~>* C H.
ptruncconntype_eq_equiv _ _ !rec_down_le_beta_ge

Definition GType_hom (G H : [n;k]GType) : Type.
B G ->* B H

Definition ωGType_hom (G H : [n;ω]GType) : pType.
pointed.MK
  (Σ(f : forall n, oB G n ->* oB H n), forall n, psquare (f n) (Ω-> (f (n+1))) (oe G n) (oe H n))
  ⟨fun n => pconst (oB G n) (oB H n), fun n => !phconst_square @vp* !ap1_pconst⟩

(* Constructions on higher groups *)
Definition Decat (G : [n+1;k]GType) : [n;k]GType.
GType.mk (ptrunctype.mk (ptrunc n G) _ (point _)) (pconntype.mk (ptrunc (n + k) (B G)) _ (point _))
  abstract begin
  refine ptrunc_pequiv_ptrunc n (e G) @e* _,
  symmetry, exact !loopn_ptrunc_pequiv_nat
Defined. end

Definition Disc (G : [n;k]GType) : [n+1;k]GType.
GType.mk (ptrunctype.mk G (show is_trunc (n.+1) G, from _) (point _)) (B G) (e G)

Definition Decat_adjoint_Disc (G : [n+1;k]GType) (H : [n;k]GType) :
  ppMap (B (Decat G)) (B H) <~>* ppMap (B G) (B (Disc H)).
pmap_ptrunc_pequiv (n + k) (B G) (B H)

Definition Decat_adjoint_Disc_natural {G G' : [n+1;k]GType} {H H' : [n;k]GType}
  (g : B G' ->* B G) (h : B H ->* B H') :
  psquare (Decat_adjoint_Disc G H)
  (Decat_adjoint_Disc G' H')
  (ppcompose_left h o* ppcompose_right (ptrunc_functor _ g))
  (ppcompose_left h o* ppcompose_right g).
pmap_ptrunc_pequiv_natural (n + k) g h

Definition Decat_Disc (G : [n;k]GType) : Decat (Disc G) = G.
GType_eq !ptrunc_pequiv

Definition InfDecat (n : ℕ) (G : [∞;k]GType) : [n;k]GType.
GType.mk (ptrunctype.mk (ptrunc n G) _ (point _)) (pconntype.mk (ptrunc (n + k) (iB G)) _ (point _))
  abstract begin
  refine ptrunc_pequiv_ptrunc n (ie G) @e* _,
  symmetry, exact !loopn_ptrunc_pequiv_nat
Defined. end

Definition InfDisc (n : ℕ) (G : [n;k]GType) : [∞;k]GType.
InfGType.mk G (B G) (e G)

Definition InfDecat_adjoint_InfDisc (G : [∞;k]GType) (H : [n;k]GType) :
  ppMap (B (InfDecat n G)) (B H) <~>* ppMap (iB G) (iB (InfDisc n H)).
pmap_ptrunc_pequiv (n + k) (iB G) (B H)

Definition InfDecat_adjoint_InfDisc_natural {G G' : [∞;k]GType} {H H' : [n;k]GType}
  (g : iB G' ->* iB G) (h : B H ->* B H') :
  psquare (InfDecat_adjoint_InfDisc G H)
  (InfDecat_adjoint_InfDisc G' H')
  (ppcompose_left h o* ppcompose_right (ptrunc_functor _ g))
  (ppcompose_left h o* ppcompose_right g).
pmap_ptrunc_pequiv_natural (n + k) g h

Definition InfDecat_InfDisc (G : [n;k]GType) : InfDecat n (InfDisc n G) = G.
GType_eq !ptrunc_pequiv

Definition Deloop (G : [n;k+1]GType) : [n+1;k]GType.
have is_conn k (B G), from is_conn_pconntype (B G),
have is_trunc (n + (k + 1)) (B G), from is_trunc_B G,
have is_trunc ((n + 1) + k) (B G), from transport (fun (n : ℕ) => is_trunc n _) (succ_add n k)^-1 this,
GType.mk (ptrunctype.mk (Ω[k] (B G)) !is_trunc_loopn_nat (point _))
  (pconntype.mk (B G) !is_conn_of_is_conn_succ (point _))
  (pequiv_of_equiv erfl idp)

Definition Loop (G : [n+1;k]GType) : [n;k+1]GType.
GType.mk (ptrunctype.mk (loops G) !is_trunc_loop_nat (point _))
  (connconnect k (B G))
  (loop_pequiv_loop (e G) @e* (loopn_connect k (B G))^-1ᵉ*)

Definition Deloop_adjoint_Loop (G : [n;k+1]GType) (H : [n+1;k]GType) :
  ppMap (B (Deloop G)) (B H) <~>* ppMap (B G) (B (Loop H)).
(connect_intro_pequiv _ !is_conn_pconntype)^-1ᵉ*

Definition Deloop_adjoint_Loop_natural {G G' : [n;k+1]GType} {H H' : [n+1;k]GType}
  (g : B G' ->* B G) (h : B H ->* B H') :
  psquare (Deloop_adjoint_Loop G H)
  (Deloop_adjoint_Loop G' H')
  (ppcompose_left h o* ppcompose_right g)
  (ppcompose_left (connect_functor k h) o* ppcompose_right g).
(connect_intro_pequiv_natural g h _ _)^-1ʰ*

Definition Loop_Deloop (G : [n;k+1]GType) : Loop (Deloop G) = G.
GType_eq (connect_pequiv (is_conn_pconntype (B G)))

Definition Forget (G : [n;k+1]GType) : [n;k]GType.
have is_conn k (B G), from !is_conn_pconntype,
GType.mk G (pconntype.mk (loops (B G)) !is_conn_loop (point _))
  abstract begin
  refine e G @e* !loopn_succ_in
Defined. end

Definition Stabilize (G : [n;k]GType) : [n;k+1]GType.
have is_conn k (susp (B G)), from !is_conn_susp,
have Hconn : is_conn k (ptrunc (n + k + 1) (susp (B G))), from !is_conn_ptrunc,
GType.mk (ptrunctype.mk (ptrunc n (Ω[k+1] (susp (B G)))) _ (point _))
  (pconntype.mk (ptrunc (n+k+1) (susp (B G))) Hconn (point _))
  abstract begin
  refine !loopn_ptrunc_pequiv^-1ᵉ* @e* _,
  apply loopn_pequiv_loopn,
  exact ptrunc_change_index !of_nat_add_of_nat _
Defined. end

Definition Stabilize_pequiv {G H : [n;k]GType} (e : B G <~>* B H) :
  B (Stabilize G) <~>* B (Stabilize H).
ptrunc_pequiv_ptrunc (n+k+1) (susp_pequiv e)

Definition Stabilize_adjoint_Forget (G : [n;k]GType) (H : [n;k+1]GType) :
  ppMap (B (Stabilize G)) (B H) <~>* ppMap (B G) (B (Forget H)).
have is_trunc (n + k + 1) (B H), from !is_trunc_B,
pmap_ptrunc_pequiv (n + k + 1) (⅀ (B G)) (B H) @e* susp_adjoint_loop (B G) (B H)

Definition Stabilize_adjoint_Forget_natural {G G' : [n;k]GType} {H H' : [n;k+1]GType}
  (g : B G' ->* B G) (h : B H ->* B H') :
  psquare (Stabilize_adjoint_Forget G H)
  (Stabilize_adjoint_Forget G' H')
  (ppcompose_left h o* ppcompose_right (ptrunc_functor (n+k+1) (⅀-> g)))
  (ppcompose_left (Ω-> h) o* ppcompose_right g).
Proof.
  have is_trunc (n + k + 1) (B H), from !is_trunc_B,
  have is_trunc (n + k + 1) (B H'), from !is_trunc_B,
  refine pmap_ptrunc_pequiv_natural (n+k+1) (⅀-> g) h @h* _,
  exact susp_adjoint_loop_natural_left g @v* susp_adjoint_loop_natural_right h
Defined.

Definition Forget_Stabilize (H : k ≥ n + 2) (G : [n;k]GType) : B (Forget (Stabilize G)) <~>* B G.
loop_ptrunc_pequiv _ _ @e*
Proof.
  cases k with k,
  { cases H },
  { have k ≥ succ n, from le_of_succ_le_succ H,
  assert this : n + succ k ≤ 2 * k,
  { rewrite [two_mul, add_succ, -succ_add], exact nat.add_le_add_right this k },
  exact freudenthal_pequiv this (B G) }
Defined.^-1ᵉ* @e*
ptrunc_pequiv (n + k) _

Definition Stabilize_Forget (H : k ≥ n + 1) (G : [n;k+1]GType) : B (Stabilize (Forget G)) <~>* B G.
Proof.
  assert lem1 : n + succ k ≤ 2 * k,
  { rewrite [two_mul, add_succ, -succ_add], exact nat.add_le_add_right H k },
  have is_conn k (B G), from !is_conn_pconntype,
  have forall (G' : [n;k+1]GType), is_trunc (n + k + 1) (B G'), from is_trunc_B,
  note z . is_conn_fun_loop_susp_counit (B G) (nat.le_refl (2 * k)) =>
  refine ptrunc_pequiv_ptrunc_of_le (of_nat_le_of_nat lem1) (@(ptrunc_pequiv_ptrunc_of_is_conn_fun _ _) z) @e*
  !ptrunc_pequiv,
Defined.

Definition stabilization (H : k ≥ n + 2) : is_equiv (@Stabilize n k).
Proof.
  fapply adjointify,
  { exact Forget },
  { intro G, apply GType_eq, exact Stabilize_Forget (le.trans !self_le_succ H) _ },
  { intro G, apply GType_eq, exact Forget_Stabilize H G }
Defined.

(* an incomplete formalization of ω-Stabilization *)
Definition ωForget (k : ℕ) (G : [n;ω]GType) : [n;k]GType.
have is_trunc (n + k) (oB G k), from _,
have is_trunc n (Ω[k] (oB G k)), from !is_trunc_loopn_nat,
GType.mk (ptrunctype.mk (Ω[k] (oB G k)) _ (point _)) (oB G k) (pequiv_of_equiv erfl idp)

Definition nStabilize (H : k ≤ l) (G : GType.{u} n k) : GType.{u} n l.
Proof.
  induction H with l H IH, exact G, exact Stabilize IH
Defined.

Definition nStabilize_pequiv (H H' : k ≤ l) {G G' : [n;k]GType}
  (e : B G <~>* B G') : B (nStabilize H G) <~>* B (nStabilize H' G').
Proof.
  induction H with l H IH,
  { exact e @e* pequiv_ap (fun H => B (nStabilize H G')) (is_prop.elim (le.refl k) H') },
  cases H' with l H'',
  { exfalso, exact not_succ_le_self H },
  exact Stabilize_pequiv (IH H'')
Defined.

Definition nStabilize_pequiv_of_eq (H : k ≤ l) (p : k = l) (G : [n;k]GType) :
  B (nStabilize H G) <~>* B G.
Proof. induction p, exact pequiv_ap (fun H => B (nStabilize H G)) (is_prop.elim H (le.refl k)) end

Definition ωStabilize_of_le (H : k ≥ n + 2) (G : [n;k]GType) : [n;ω]GType.
ωGType.mk_le k (fun l H' => GType_equiv n l (nStabilize H' G))
  (fun l H' => (Forget_Stabilize (le.trans H H') (nStabilize H' G))^-1ᵉ*)

Definition ωStabilize_of_le_beta (H : k ≥ n + 2) (G : [n;k]GType) (H' : l ≥ k) :
  oB (ωStabilize_of_le H G) l <~>* GType_equiv n l (nStabilize H' G).
ptruncconntype_eq_equiv _ _ !rec_down_le_beta_ge

Definition ωStabilize_of_le_pequiv (H : k ≥ n + 2) (H' : k' ≥ n + 2) {G : [n;k]GType}
  {G' : [n;k']GType} (e : B G <~>* B G') (l : ℕ) (Hl : l ≥ k) (Hl' : l ≥ k') (p : k = k') :
  oB (ωStabilize_of_le H G) l <~>* oB (ωStabilize_of_le H' G') l.
Proof.
  refine ωStabilize_of_le_beta H G Hl @e* _ @e* (ωStabilize_of_le_beta H' G' Hl')^-1ᵉ*,
  induction p,
  exact nStabilize_pequiv _ _ e
Defined.

Definition ωForget_ωStabilize_of_le (H : k ≥ n + 2) (G : [n;k]GType) :
  B (ωForget k (ωStabilize_of_le H G)) <~>* B G.
ωStabilize_of_le_beta H _ (le.refl k)

Definition ωStabilize (G : [n;k]GType) : [n;ω]GType.
ωStabilize_of_le !le_max_left (nStabilize !le_max_right G)

Definition ωForget_ωStabilize (H : k ≥ n + 2) (G : [n;k]GType) :
  B (ωForget k (ωStabilize G)) <~>* B G.
Proof.
  refine _ @e* ωForget_ωStabilize_of_le H G,
  esimp [ωForget, ωStabilize],
  have H' : max (n + 2) k = k, from max_eq_right H,
  exact ωStabilize_of_le_pequiv !le_max_left H (nStabilize_pequiv_of_eq _ H'^-1 _)
  k (le_of_eq H') (le.refl k) H'
Defined.

(*
Definition ωStabilize_adjoint_ωForget (G : [n;k]GType) (H : [n;ω]GType) :
  ωGType_hom (ωStabilize G) H <~>* ppMap (B G) (B (ωForget k H)).
sorry

Definition ωStabilize_ωForget (G : [n;ω]GType) (l : ℕ) :
  oB (ωStabilize (ωForget k G)) l <~>* oB G l.
Proof.
  exact sorry
Defined.

Definition ωstabilization (H : k ≥ n + 2) : is_equiv (@ωStabilize n k).
Proof.
  apply adjointify _ (ωForget k),
  { intro G', exact sorry },
  { intro G, apply GType_eq, exact ωForget_ωStabilize H G }
Defined.
*)

Definition is_trunc_GType_hom (G H : [n;k]GType) : is_trunc n (GType_hom G H).
is_trunc_pmap_of_is_conn _ (k.-2) _ _ (k + n) _ (le_of_eq (sub_one_add_plus_two_sub_one k n)^-1)
  (is_trunc_B' H)

Definition is_set_GType_hom (G H : [0;k]GType) : is_set (GType_hom G H).
is_trunc_GType_hom G H

Definition is_trunc_GType (n k : ℕ) : is_trunc (n + 1) [n;k]GType.
Proof.
  apply @is_trunc_equiv_closed_rev _ _ (n + 1) (GType_equiv n k),
  apply is_trunc_succ_intro, intros X Y,
  apply @is_trunc_equiv_closed_rev _ _ _ (ptruncconntype_eq_equiv X Y),
  apply @is_trunc_equiv_closed_rev _ _ _ (pequiv.sigma_char_pmap X Y),
  apply @is_trunc_subtype (X ->* Y) (fun f => trunctype.mk' -1 (is_equiv f)),
  exact is_trunc_GType_hom ((GType_equiv n k)^-1ᵉ X) ((GType_equiv n k)^-1ᵉ Y)
Defined.

local attribute [instance] is_set_GType_hom

Definition cGType (k : ℕ) : Precategory.
pb_Precategory (cptruncconntype' (k.-1))
  (GType_equiv 0 k @e ptruncconntype_equiv (ap of_nat (zero_add k)) idp @e
  (ptruncconntype'_equiv_ptruncconntype (k.-1))^-1ᵉ)

example (k : ℕ) : Precategory.carrier (cGType k) = [0;k]GType . by reflexivity
example (k : ℕ) (G H : cGType k) : (G ⟶ H) = (B G ->* B H) . by reflexivity

Definition cGType_equivalence_cType (k : ℕ) : cGType k <~>c cpType[k.-1].
!pb_Precategory_equivalence_of_equiv

Definition cGType_equivalence_Grp : cGType.{u} 1 <~>c Grp.{u}.
equivalence.trans !pb_Precategory_equivalence_of_equiv
  (equivalence.trans (equivalence.symm Grp_equivalence_cptruncconntype')
  proof equivalence.refl _ qed)

Definition cGType_equivalence_AbGrp (k : ℕ) : cGType.{u} (k+2) <~>c AbGrp.{u}.
equivalence.trans !pb_Precategory_equivalence_of_equiv
  (equivalence.trans (equivalence.symm (AbGrp_equivalence_cptruncconntype' k))
  proof equivalence.refl _ qed)

(*
print axioms GType_equiv
print axioms InfGType_equiv
print axioms Decat_adjoint_Disc
print axioms Decat_adjoint_Disc_natural
print axioms InfDecat_adjoint_InfDisc
print axioms InfDecat_adjoint_InfDisc_natural
print axioms Deloop_adjoint_Loop
print axioms Deloop_adjoint_Loop_natural
print axioms Stabilize_adjoint_Forget
print axioms Stabilize_adjoint_Forget_natural
print axioms stabilization
print axioms is_trunc_GType
print axioms cGType_equivalence_Grp
print axioms cGType_equivalence_AbGrp
*)

Defined. higher_group
