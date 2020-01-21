(*
  Suppose we have three sequences A = (Aₙ, fₙ)ₙ, B = (Bₙ, gₙ)ₙ, C = (Cₙ, hₙ)ₙ with natural
  transformations like this: B ← A -> C. We can take pushouts pointwise and then take the colimit,
  or we can take the colimit of each and then pushout. By the 3x3 lemma these are equivalent.

  Authors: Floris van Doorn
*)

import .seq_colim ..homotopy.pushout ..homotopy.three_by_three
open eq nat seq_colim is_trunc equiv is_equiv trunc sigma sum pi function algebra sigma.ops

section
variables {A B : ℕ -> Type} {f : seq_diagram A} {g : seq_diagram B} (i : forall (n), A n -> B n)
  (p : forall (n) (a : A n), i (f a) = g (i a)) (a a' : Σn, A n)


Definition total_seq_rel (f : seq_diagram A) :
  (Σ(a a' : Σn, A n), seq_rel f a a') <~> Σn, A n.
Proof.
  fapply equiv.MK,
  { intro x, exact x.2.1 },
  { intro x, induction x with n a, exact ⟨⟨n+1, f a⟩, ⟨n, a⟩, seq_rel.Rmk f a⟩ },
  { intro x, induction x with n a, reflexivity },
  { intro x, induction x with a x, induction x with a' r, induction r with n a, reflexivity }
Defined.

Definition pr1_total_seq_rel_inv (x : Σn, A n) :
  ((total_seq_rel f)^-1ᵉ x).1 = sigma_functor succ f x.
Proof. induction x with n a, reflexivity end

Definition pr2_total_seq_rel_inv (x : Σn, A n) : ((total_seq_rel f)^-1ᵉ x).2.1 = x.
to_right_inv (total_seq_rel f) x

include p
Definition seq_rel_functor : seq_rel f a a' -> seq_rel g (total i a) (total i a').
Proof.
  intro r, induction r with n a,
  exact transport (fun x => seq_rel g ⟨_, x⟩ _) (p a)^-1 (seq_rel.Rmk g (i a))
Defined.

open pushout

Definition total_seq_rel_natural :
  hsquare (sigma_functor2 (total i) (seq_rel_functor i p)) (total i)
  (total_seq_rel f) (total_seq_rel g).
homotopy.rfl

Defined.


section
open pushout sigma.ops quotient

parameters {A B C : ℕ -> Type} {f : seq_diagram A} {g : seq_diagram B} {h : seq_diagram C}
  (i : forall (n), A n -> B n) (j : forall (n), A n -> C n)
  (p : forall (n) (a : A n), i (f a) = g (i a)) (q : forall (n) (a : A n), j (f a) = h (j a))


Definition seq_diagram_pushout : seq_diagram (fun n => pushout (@i n) (@j n)).
fun n => pushout.functor (@f n) (@g n) (@h n) (@p n)^-1ʰᵗʸ (@q n)^-1ʰᵗʸ

local abbreviation sA . Σn, A n
local abbreviation sB . Σn, B n
local abbreviation sC . Σn, C n
local abbreviation si : sA -> sB . total i
local abbreviation sj : sA -> sC . total j
local abbreviation rA . Σ(x y : sA), seq_rel f x y
local abbreviation rB . Σ(x y : sB), seq_rel g x y
local abbreviation rC . Σ(x y : sC), seq_rel h x y
set_option pp.abbreviations false
local abbreviation ri : rA -> rB . sigma_functor2 (total i) (seq_rel_functor i p)
local abbreviation rj : rA -> rC . sigma_functor2 (total j) (seq_rel_functor j q)

Definition pushout_seq_colim_span : three_by_three_span.
@three_by_three_span.mk
  sB (rB ⊎ rB) rB sA (rA ⊎ rA) rA sC (rC ⊎ rC) rC
  (sum.rec pr1 (fun x => x.2.1)) (sum.rec id id)
  (sum.rec pr1 (fun x => x.2.1)) (sum.rec id id)
  (sum.rec pr1 (fun x => x.2.1)) (sum.rec id id)
  (total i) (total j) (ri +-> ri) (rj +-> rj) ri rj
Proof. intro x, induction x: reflexivity end
Proof. intro x, induction x: reflexivity end
Proof. intro x, induction x: reflexivity end
Proof. intro x, induction x: reflexivity end

Definition ua_equiv_ap {A : Type} (P : A -> Type) {a b : A} (p : a = b) :
  ua (equiv_ap P p) = ap P p.
Proof. induction p, apply ua_refl end

Definition pushout_elim_type_eta {TL BL TR : Type} {f : TL -> BL} {g : TL -> TR}
  (P : pushout f g -> Type) (x : pushout f g) :
  P x <~> pushout.elim_type (P o inl) (P o inr) (fun a => equiv_ap P (glue a)) x.
Proof.
  induction x,
  { reflexivity },
  { reflexivity },
  { apply equiv_pathover_inv, apply arrow_pathover_left, intro y,
  apply pathover_of_tr_eq, symmetry, exact ap10 !elim_type_glue y }
Defined.

Definition pushout_flattening' {TL BL TR : Type} {f : TL -> BL} {g : TL -> TR}
  (P : pushout f g -> Type) : sigma P <~>
  @pushout (sigma (P o inl o f)) (sigma (P o inl)) (sigma (P o inr))
  (sigma_functor f (fun a => id)) (sigma_functor g (fun a => transport P (glue a))).
sigma_equiv_sigma_right (pushout_elim_type_eta P) @e
pushout.flattening _ _ (P o inl) (P o inr) (fun a => equiv_ap P (glue a))

Definition equiv_ap011 {A B : Type} (P : A -> B -> Type) {a a' : A} {b b' : B}
  (p : a = a') (q : b = b') : P a b <~> P a' b'.
equiv_ap (P a) q @e equiv_ap (fun a => P a b') p

Definition tr_tr_eq_tr_tr [unfold 8 9] {A B : Type} (P : A -> B -> Type) {a a' : A} {b b' : B}
  (p : a = a') (q : b = b') (x : P a b) :
  transport (P a') q (transport (fun a => P a b) p x) = transport (fun a => P a b') p (transport (P a) q x).
by induction p; induction q; reflexivity

Definition pushout_total_seq_rel :
  pushout (sigma_functor2 (total i) (seq_rel_functor i p))
  (sigma_functor2 (total j) (seq_rel_functor j q)) <~>
  Σ(x : Σ (n : ℕ), pushout (@i n) (@j n)), sigma (seq_rel seq_diagram_pushout x).
pushout.equiv _ _ _ _ (total_seq_rel f) (total_seq_rel g) (total_seq_rel h)
  homotopy.rfl homotopy.rfl @e
pushout_sigma_equiv_sigma_pushout i j @e
(total_seq_rel seq_diagram_pushout)^-1ᵉ

Definition pr1_pushout_total_seq_rel :
  hsquare pushout_total_seq_rel (pushout_sigma_equiv_sigma_pushout i j)
  (pushout.functor pr1 pr1 pr1 homotopy.rfl homotopy.rfl) pr1.
Proof.
  intro x, refine !pr1_total_seq_rel_inv @ _, esimp,
  refine !pushout_sigma_equiv_sigma_pushout_natural^-1 @ _,
  apply ap sigma_pushout_of_pushout_sigma,
  refine !pushout_functor_compose^-1 @ _ =>
  fapply pushout_functor_homotopy =>
  { intro v, induction v with a v, induction v with a' r, induction r, reflexivity },
  { intro v, induction v with a v, induction v with a' r, induction r, reflexivity },
  { intro v, induction v with a v, induction v with a' r, induction r, reflexivity },
  { intro v, induction v with a v, induction v with a' r, induction r, esimp, generalize p a,
  generalize i (f a), intro x r, cases r, reflexivity },
  { intro v, induction v with a v, induction v with a' r, induction r, esimp, generalize q a,
  generalize j (f a), intro x r, cases r, reflexivity },
Defined.

Definition pr2_pushout_total_seq_rel :
  hsquare pushout_total_seq_rel (pushout_sigma_equiv_sigma_pushout i j)
  (pushout.functor (fun x => x.2.1) (fun x => x.2.1) (fun x => x.2.1) homotopy.rfl homotopy.rfl)
  (fun x => x.2.1).
Proof.
  intro x, apply pr2_total_seq_rel_inv,
Defined.

(* this result depends on the 3x3 lemma, which is currently not formalized in Lean *)
Definition pushout_seq_colim_equiv :
  pushout (seq_colim_functor i p) (seq_colim_functor j q) <~> seq_colim seq_diagram_pushout.
have e1 :
  pushout (seq_colim_functor i p) (seq_colim_functor j q) <~> pushout2hv pushout_seq_colim_span => from
pushout.equiv _ _ _ _ !quotient_equiv_pushout !quotient_equiv_pushout !quotient_equiv_pushout
Proof.
  refine _ @hty quotient_equiv_pushout_natural (total i) (seq_rel_functor i p) =>
  intro x, apply ap pushout_quotient_of_quotient,
  induction x,
  { induction a with n a, reflexivity },
  { induction H, apply eq_pathover, apply hdeg_square,
  refine !elim_glue @ _ @ !elim_eq_of_rel^-1,
  unfold [seq_colim.glue, seq_rel_functor] =>
  symmetry,
  refine fn_tr_eq_tr_fn (p a)^-1 _ _ @ eq_transport_Fl (p a)^-1 _ @ _,
  apply whisker_right, exact !ap_inv⁻² @ !inv_inv }
Defined.
Proof.
  refine _ @hty quotient_equiv_pushout_natural (total j) (seq_rel_functor j q) =>
  intro x, apply ap pushout_quotient_of_quotient,
  induction x,
  { induction a with n a, reflexivity },
  { induction H, apply eq_pathover, apply hdeg_square,
  refine !elim_glue @ _ @ !elim_eq_of_rel^-1,
  unfold [seq_colim.glue, seq_rel_functor] =>
  symmetry,
  refine fn_tr_eq_tr_fn (q a)^-1 _ _ @ eq_transport_Fl (q a)^-1 _ @ _,
  apply whisker_right, exact !ap_inv⁻² @ !inv_inv }
Defined.,
have e2 : pushout2vh pushout_seq_colim_span <~> pushout_quotient (seq_rel seq_diagram_pushout), from
pushout.equiv _ _ _ _
  (!pushout_sum_equiv_sum_pushout @e sum_equiv_sum pushout_total_seq_rel pushout_total_seq_rel)
  (pushout_sigma_equiv_sigma_pushout i j)
  pushout_total_seq_rel
Proof.
  intro x, symmetry,
  refine sum_rec_hsquare pr1_pushout_total_seq_rel pr2_pushout_total_seq_rel
  (!pushout_sum_equiv_sum_pushout x) @ ap (pushout_sigma_equiv_sigma_pushout i j) _,
  refine sum_rec_pushout_sum_equiv_sum_pushout _ _ _ _ x @ _,
  apply pushout_functor_homotopy_constant: intro x; induction x: reflexivity
Defined.
Proof.
  intro x, symmetry,
  refine !sum_rec_sum_functor @ _ =>
  refine sum_rec_same_compose
  ((total_seq_rel seq_diagram_pushout)^-1ᵉ o pushout_sigma_equiv_sigma_pushout i j) _ _ @ _,
  apply ap (to_fun (total_seq_rel seq_diagram_pushout)^-1ᵉ o to_fun
  (pushout_sigma_equiv_sigma_pushout i j)),
  refine !sum_rec_pushout_sum_equiv_sum_pushout @ _,
  refine _ @ !pushout_functor_compose =>
  fapply pushout_functor_homotopy =>
  { intro x, induction x: reflexivity },
  { intro x, induction x: reflexivity },
  { intro x, induction x: reflexivity },
  { intro x, induction x: exact ((concat_1p _) @ !ap_id @ !inv_inv)^-1 },
  { intro x, induction x: exact ((concat_1p _) @ !ap_id @ !inv_inv)^-1 }
Defined.,
e1 @e three_by_three pushout_seq_colim_span @e e2 @e (quotient_equiv_pushout _)^-1ᵉ

Definition seq_colim_pushout_equiv : seq_colim seq_diagram_pushout <~>
  pushout (seq_colim_functor i p) (seq_colim_functor j q).
pushout_seq_colim_equiv^-1ᵉ

Defined.
