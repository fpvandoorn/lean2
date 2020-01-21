(*
Copyright (c) 2016-2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz

Various groups of maps. Most importantly we define a group structure
on trunc 0 (A ->* loops B) and the dependent version trunc 0 (ppi _ _),
which are used in theDefinition of cohomology.
*)

import algebra.group_theory ..pointed ..pointed_pi eq2 .product_group
open pi pointed algebra group eq equiv is_trunc trunc susp nat function
namespace group

  (* Group of dependent functions into a loop space *)
Definition ppi_mul {A : pType} {B : A -> pType} (f g : ppforall a, loops (B a)) : ppforall a, loops (B a).
  proof ppi.mk (fun a => f a @ g a) (point_eq f ◾ point_eq g @ (concat_1p _)) qed

Definition ppi_inv {A : pType} {B : A -> pType} (f : ppforall a, loops (B a)) : ppforall a, loops (B a).
  proof ppi.mk (fun a => (f a)^-1ᵖ) (point_eq f)⁻² qed

Definition inf_pgroup_pppi {A : pType} (B : A -> pType) :
  inf_pgroup (ppforall a, loops (B a)).
Proof.
  fapply inf_pgroup.mk,
  { exact ppi_mul },
  { intro f g h, apply path_pforall, fapply Build_pHomotopy,
  { intro a, exact con.assoc (f a) (g a) (h a) },
  { symmetry, rexact eq_of_square (con2_assoc (point_eq f) (point_eq g) (point_eq h)) }},
  { exact ppi_inv },
  { intros f, apply path_pforall, fapply Build_pHomotopy,
  { intro a, exact one_mul (f a) },
  { symmetry, apply eq_of_square, refine _ @vp !ap_id, apply natural_square_tr }},
  { intros f, apply path_pforall, fapply Build_pHomotopy,
  { intro a, exact mul_one (f a) },
  { reflexivity }},
  { intro f, apply path_pforall, fapply Build_pHomotopy,
  { intro a, exact con.left_inv (f a) },
  { exact !con_left_inv_idp }},
Defined.
  (* inf_pgroup_pequiv_closed (loop_pppi_pequiv B) _ *)

Definition inf_group_ppi {A : pType} (B : A -> pType) : inf_group (ppforall a, loops (B a)).
  @inf_group_of_inf_pgroup _ (inf_pgroup_pppi B)

Definition gppi_loop {A : pType} (B : A -> pType) : InfGroup.
  InfGroup.mk (ppforall a, loops (B a)) (inf_group_ppi B)

Definition gppi_loopn (n : ℕ) [H : is_succ n] {A : pType} (B : A -> pType) : InfGroup.
  InfGroup.mk (ppforall a, Ω[n] (B a)) (by induction H with n; exact inf_group_ppi (Ω[n] o B))

Definition Group_trunc_ppi {A : pType} (B : A -> pType) : Group.
  gtrunc (gppi_loop B)

Definition ab_inf_group_ppi {A : pType} (B : A -> pType) :
  ab_inf_group (ppforall a, loops (loops (B a))).
  (ab_inf_group, inf_group_ppi (fun a => loops (B a)), mul_comm.
Proof.
  intro f g, apply path_pforall, fapply Build_pHomotopy,
  { intro a, exact eckmann_hilton (f a) (g a) },
  { symmetry, rexact eq_of_square (eckmann_hilton_con2 (point_eq f) (point_eq g)) }
Defined.)

Definition agppi_loop {A : pType} (B : A -> pType) : AbInfGroup.
  AbInfGroup.mk (ppforall a, loops (loops (B a))) (ab_inf_group_ppi B)

Definition AbGroup_trunc_ppi {A : pType} (B : A -> pType) : AbGroup.
  agtrunc (agppi_loop B)

  (*Definition trunc_ppi_isomorphic_pmap (A B : pType) *)
  (*   : Group.mk (trunc 0 (ppforall (a : A), loops B)) !group_trunc *)
  (*     <~>g Group.mk (trunc 0 (A ->* loops B)) !group_trunc . *)
  (* begin *)
  (*   reflexivity, *)
  (*   (* apply trunc_isomorphism_of_equiv (pppi_equiv_pmap A (loops B)), *) *)
  (*   (* intro h k, induction h with h h_pt, induction k with k k_pt, reflexivity *) *)
  (* end *)

  universe variables u v

  variables {A : pType.{u}} {B : A -> Type.{v}} {x₀ : B (point _)} {k l m : ppi B x₀}

Definition phomotopy_path_homomorphism (p : k = l) (q : l = m)
  : phomotopy_path (p @ q) = phomotopy_path p @* phomotopy_path q.
Proof.
  induction q, induction p, induction k with k q, induction q, reflexivity
Defined.

  protectedDefinition ppi_mul_loop.lemma1 {X : Type} {x : X} (p q : x = x) (p_pt : idp = p) (q_pt : idp = q)
  : refl (p @ q) @ whisker_left p q_pt^-1 @ p_pt^-1 = p_pt^-1 ◾ q_pt^-1.
  by induction p_pt; induction q_pt; reflexivity

  protectedDefinition ppi_mul_loop.lemma2 {X : Type} {x : X} (p q : x = x) (p_pt : p = idp) (q_pt : q = idp)
  : refl (p @ q) @ whisker_left p q_pt @ p_pt = p_pt ◾ q_pt.
  by rewrite [-(inv_inv p_pt),-(inv_inv q_pt)]; exact ppi_mul_loop.lemma1 p q p_pt^-1 q_pt^-1

Definition ppi_mul_loop {h : forall a, B a} (f g : ppi.mk h idp ==* ppi.mk h idp) : f @* g = ppi_mul f g.
Proof.
  apply ap (ppi.mk (fun a => f a @ g a)),
  apply ppi.rec_on f, intros f' f_pt, apply ppi.rec_on g, intros g' g_pt,
  clear f g, esimp at *, exact ppi_mul_loop.lemma2 (f' (point _)) (g' (point _)) f_pt g_pt
Defined.

Definition gloop_ppi_isomorphism_gen (k : ppi B x₀) :
  Ωg (pointed.Mk k) <~>∞g gppi_loop (fun a => pointed.Mk (ppi.to_fun k a)).
Proof.
  apply inf_isomorphism_of_equiv (ppi_loop_equiv k),
  intro f g, induction k with k p, induction p,
  apply trans (phomotopy_path_homomorphism f g),
  exact ppi_mul_loop (phomotopy_path f) (phomotopy_path g)
Defined.

Definition gloop_ppi_isomorphism (B : A -> pType) : Ωg (ppforall a, B a) <~>∞g gppi_loop B.
  proof gloop_ppi_isomorphism_gen (ppi_const B) qed

Definition gloopn_ppi_isomorphism (n : ℕ) [H : is_succ n] (B : A -> pType) :
  Ωg[n] (ppforall a, B a) <~>∞g gppi_loopn n B.
Proof.
  induction H with n, induction n with n IH,
  { exact gloop_ppi_isomorphism B },
  { exact Ωg<~> (pequiv_of_inf_isomorphism IH) @∞g gloop_ppi_isomorphism (Ω[succ n] o B) }
Defined.

Definition trunc_ppi_loop_isomorphism_gen (k : ppi B x₀) :
  gtrunc (gloop (pointed.Mk k)) <~>g gtrunc (gppi_loop (fun a => pointed.Mk (k a))).
  gtrunc_isomorphism_gtrunc (gloop_ppi_isomorphism_gen k)

Definition trunc_ppi_loop_isomorphism (B : A -> pType) :
  gtrunc (gloop (ppforall (a : A), B a)) <~>g gtrunc (gppi_loop B).
  proof trunc_ppi_loop_isomorphism_gen (ppi_const B) qed

Definition gppi_loop_homomorphism_right {A : pType} {B B' : A -> pType}
  (g : forall a, B a ->* B' a) : gppi_loop B ->∞g gppi_loop B'.
  gloop_ppi_isomorphism B' o∞g Ωg-> (pppi_compose_left g) o∞g (gloop_ppi_isomorphism B)^-1ᵍ⁸


  (* We first define the group structure on A ->* loops B (except for truncatedness).
  Instead of loops B, we could also choose any infinity group. However, we need various 2-coherences,
  so it's easier to just do it for the loop space. *)
Definition pmap_mul {A B : pType} (f g : A ->* loops B) : A ->* loops B.
  ppi_mul f g

Definition pmap_inv {A B : pType} (f : A ->* loops B) : A ->* loops B.
  ppi_inv f

  (* we prove some coherences of the multiplication. We don't need them for the group structure,
  but they are used to show that cohomology satisfies the Eilenberg-Steenrod axioms *)
Definition ap1_pmap_mul {X Y : pType} (f g : X ->* loops Y) :
  Ω-> (pmap_mul f g) ==* pmap_mul (Ω-> f) (Ω-> g).
Proof.
  fapply Build_pHomotopy,
  { intro p, esimp,
  refine ap1_gen_con_left (point_eq f) (point_eq f)
  (point_eq g) (point_eq g) p @ _,
  refine !whisker_right_idp ◾ !whisker_left_idp2, },
  { refine (concat_pp_p _ _ _) @ _,
  refine _ ◾ idp @ _, rotate 1,
  rexact ap1_gen_con_left_idp (point_eq f) (point_eq g), esimp,
  refine (concat_pp_p _ _ _) @ _,
  apply whisker_left, apply inv_con_eq_idp,
  refine !con2_con_con2 @ ap011 concat2 _ _:
  refine eq_of_square (!natural_square @hp !ap_id) @ (concat_p1 _) }
Defined.

Definition pmap_mul_pcompose {A B C : pType} (g h : B ->* loops C) (f : A ->* B) :
  pmap_mul g h o* f ==* pmap_mul (g o* f) (h o* f).
Proof.
  fapply Build_pHomotopy,
  { intro p, reflexivity },
  { esimp, refine (concat_1p _) @ _, refine !con2_con_con2^-1 @ whisker_right _ _,
  refine !ap_eq_ap011^-1 }
Defined.

Definition pcompose_pmap_mul {A B C : pType} (h : B ->* C) (f g : A ->* loops B) :
  Ω-> h o* pmap_mul f g ==* pmap_mul (Ω-> h o* f) (Ω-> h o* g).
Proof.
  fapply Build_pHomotopy,
  { intro p, exact ap1_con h (f p) (g p) },
  { refine whisker_left _ !con2_con_con2^-1 @ _, refine (concat_pp_p _ _ _)^-1 @ _,
  refine whisker_right _ (eq_of_square !ap1_gen_con_natural) @ _,
  refine (concat_pp_p _ _ _) @ whisker_left _ _, apply ap1_gen_con_idp }
Defined.

Definition loop_susp_intro_pmap_mul {X Y : pType} (f g : susp X ->* loops Y) :
  loop_susp_intro (pmap_mul f g) ==* pmap_mul (loop_susp_intro f) (loop_susp_intro g).
  pwhisker_right _ !ap1_pmap_mul @* !pmap_mul_pcompose

Definition gpmap_loop (A B : pType) : InfGroup.
  InfGroup.mk (A ->* loops B) !inf_group_ppi

Definition gpmap_loopn (n : ℕ) [H : is_succ n] (A B : pType) : InfGroup.
  InfGroup.mk (A ->** Ω[n] B) (by induction H with n; exact inf_group_ppi (fun a => Ω[n] B))

Definition gloop_pmap_isomorphism (A B : pType) : Ωg (A ->** B) <~>∞g gpmap_loop A B.
  gloop_ppi_isomorphism _

Definition gloopn_pmap_isomorphism (n : ℕ) [H : is_succ n] (A B : pType) :
  Ωg[n] (A ->** B) <~>∞g gpmap_loopn n A B.
Proof.
  induction H with n, induction n with n IH,
  { exact gloop_pmap_isomorphism A B },
  { rexact Ωg<~> (pequiv_of_inf_isomorphism IH) @∞g gloop_pmap_isomorphism A (Ω[succ n] B) }
Defined.

Definition gpmap_loop' (A : pType) {B C : pType} (e : loops C <~>* B) :
  InfGroup.
  InfGroup.mk (A ->* B)
  (@inf_group_of_inf_pgroup _ (inf_pgroup_pequiv_closed (ppMap_pequiv_ppMap_right e)
  !inf_pgroup_pppi))

Definition gpmap_loop_homomorphism_right (A : pType) {B B' : pType}
  (g : B ->* B') : gpmap_loop A B ->∞g gpmap_loop A B'.
  gppi_loop_homomorphism_right (fun a => g)

Definition Group_trunc_pmap (A B : pType) : Group.
  Group.mk (trunc 0 (A ->* loops B)) (@group_trunc _ !inf_group_ppi)

Definition Group_trunc_pmap_homomorphism {A A' B : pType} (f : A' ->* A) :
  Group_trunc_pmap A B ->g Group_trunc_pmap A' B.
Proof.
  fapply homomorphism.mk,
  { apply trunc_functor => intro g, exact g o* f},
  { intro g h, induction g with g, esimp, induction h with h, apply ap tr,
  apply path_pforall, fapply Build_pHomotopy,
  { intro a, reflexivity },
  { symmetry, refine _ @ (concat_1p _)^-1,
  refine whisker_right _ (ap_pp _ _ _)_fn @ _, apply con2_con_con2 }}
Defined.

Definition Group_trunc_pmap_isomorphism {A A' B : pType} (f : A' <~>* A) :
  Group_trunc_pmap A B <~>g Group_trunc_pmap A' B.
Proof.
  apply isomorphism.mk (Group_trunc_pmap_homomorphism f),
  apply @is_equiv_trunc_functor =>
  exact to_is_equiv (ppMap_pequiv_ppMap_left f),
Defined.

Definition Group_trunc_pmap_isomorphism_refl (A B : pType) (x : Group_trunc_pmap A B) :
  Group_trunc_pmap_isomorphism (pequiv.refl A) x = x.
Proof.
  induction x, apply ap tr, apply path_pforall, apply pcompose_pid
Defined.

Definition Group_trunc_pmap_pid {A B : pType} (f : Group_trunc_pmap A B) :
  Group_trunc_pmap_homomorphism (pid A) f = f.
Proof.
  induction f with f, apply ap tr, apply path_pforall, apply pcompose_pid
Defined.

Definition Group_trunc_pmap_pconst {A A' B : pType} (f : Group_trunc_pmap A B) :
  Group_trunc_pmap_homomorphism (pconst A' A) f = 1.
Proof.
  induction f with f, apply ap tr, apply path_pforall, apply pcompose_pconst
Defined.

Definition Group_trunc_pmap_pcompose {A A' A'' B : pType} (f : A' ->* A)
  (f' : A'' ->* A') (g : Group_trunc_pmap A B) : Group_trunc_pmap_homomorphism (f o* f') g =
  Group_trunc_pmap_homomorphism f' (Group_trunc_pmap_homomorphism f g).
Proof.
  induction g with g, apply ap tr, apply path_pforall, exact !passoc^-1*
Defined.

Definition Group_trunc_pmap_phomotopy {A A' B : pType} {f f' : A' ->* A}
  (p : f ==* f') : @Group_trunc_pmap_homomorphism _ _ B f == Group_trunc_pmap_homomorphism f'.
Proof.
  intro g, induction g, exact ap tr (path_pforall (pwhisker_left a p))
Defined.

Definition Group_trunc_pmap_phomotopy_refl {A A' B : pType} (f : A' ->* A)
  (x : Group_trunc_pmap A B) : Group_trunc_pmap_phomotopy (reflexivity f) x = idp.
Proof.
  induction x,
  refine ap02 tr _,
  refine ap path_pforall _ @ !path_pforall_refl,
  apply pwhisker_left_refl
Defined.

Definition ab_inf_group_pmap [instance] (A B : pType) :
  ab_inf_group (A ->* loops (loops B)).
  !ab_inf_group_ppi

Definition ab_group_trunc_pmap [instance] (A B : pType) :
  ab_group (trunc 0 (A ->* loops (loops B))).
  !ab_group_trunc

Definition AbGroup_trunc_pmap (A B : pType) : AbGroup.
  AbGroup.mk (trunc 0 (A ->* loops (loops B))) _

  (* Group of dependent functions whose codomain is a group *)
Definition group_pi [instance] {A : Type} (P : A -> Type) [forall a, group (P a)] :
  group (forall a, P a).
Proof.
  fapply group.mk,
  { apply is_trunc_pi },
  { intro f g a, exact f a * g a },
  { intros, apply eq_of_homotopy, intro a, apply mul.assoc },
  { intro a, exact 1 },
  { intros, apply eq_of_homotopy, intro a, apply one_mul },
  { intros, apply eq_of_homotopy, intro a, apply mul_one },
  { intro f a, exact (f a)^-1 },
  { intros, apply eq_of_homotopy, intro a, apply mul.left_inv }
Defined.

Definition Group_pi {A : Type} (P : A -> Group) : Group.
  Group.mk (forall a, P a) _

  (* we use superscript in the following notation, because otherwise we can never write something
  like `forall g h : G, _` anymore *)

  notation `forall ᵍ` binders `, ` r:(scoped P, Group_pi P) . r

Definition Group_pi_intro {A : Type} {G : Group} {P : A -> Group} (f : forall a, G ->g P a)
  : G ->g forall ᵍ a, P a.
Proof.
  fconstructor,
  { intro g a, exact f a g },
  { intro g h, apply eq_of_homotopy, intro a, exact respect_mul (f a) g h }
Defined.

Definition Group_pi_eval {A : Type} (P : A -> Group) (a : A)
  : (forall ᵍ a, P a) ->g P a.
Proof.
  fconstructor,
  { intro h, exact h a },
  { intro g h, reflexivity }
Defined.

Definition Group_pi_functor {A B : Type} {P : A -> Group} {Q : B -> Group}
  (f : B -> A) (g : forall b, P (f b) ->g Q b) : (forall ᵍ a, P a) ->g forall ᵍ b, Q b.
  Group_pi_intro (fun b => g b og Group_pi_eval P (f b))

Definition Group_pi_functor_compose {A B C : Type} {P : A -> Group} {Q : B -> Group}
  {R : C -> Group} (f : B -> A) (f' : C -> B) (g' : forall c, Q (f' c) ->g R c) (g : forall b, P (f b) ->g Q b) :
  Group_pi_functor (f o f') (fun c => g' c og g (f' c)) ~
  Group_pi_functor f' g' o Group_pi_functor f g.
Proof.
  intro h, reflexivity
Defined.

  open bool prod is_equiv
Definition Group_pi_isomorphism_Group_pi {A B : Type}
  {P : A -> Group} {Q : B -> Group} (f : B <~> A) (g : forall b, P (f b) <~>g Q b) :
  (forall ᵍ a, P a) <~>g forall ᵍ b, Q b.
  isomorphism.mk (Group_pi_functor f g) (is_equiv_pi_functor f g)

Definition product_isomorphism_Group_pi (G H : Group) :
  G \*g H <~>g Group_pi (bool.rec G H).
Proof.
  fconstructor,
  { exact Group_pi_intro (bool.rec (product_pr1 G H) (product_pr2 G H)) },
  { apply adjointify _ (fun h => (h ff, h tt)),
  { intro h, apply eq_of_homotopy, intro b, induction b: reflexivity },
  { intro gh, induction gh, reflexivity }}
Defined.



Defined. group
