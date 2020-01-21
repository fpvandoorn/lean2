(*
Copyright (c) 2017 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egbert Rijke

Basic facts about short exact sequences.

At the moment, it only covers short exact sequences of abelian groups, but this should be extended to short exact sequences in any abelian category.
*)

import algebra.group_theory hit.set_quotient types.sigma types.list types.sum .quotient_group .subgroup .exactness

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod prod.ops sum list trunc function group trunc
  equiv is_equiv property

structure SES (A B C : AbGroup).
  ( f : A ->g B)
  ( g : B ->g C)
  ( Hf : is_embedding f)
  ( Hg : is_surjective g)
  ( ex : is_exact_ag f g)

Definition SES_of_inclusion {A B : AbGroup} (f : A ->g B) (Hf : is_embedding f) : SES A B (quotient_ab_group (image f)).
Proof.
  have Hg : is_surjective (ab_qg_map (image f)),
  from is_surjective_ab_qg_map (image f),
  fapply SES.mk,
  exact f,
  exact ab_qg_map (image f),
  exact Hf,
  exact Hg,
  fapply is_exact.mk,
  intro a,
  fapply ab_qg_map_eq_one, fapply tr, fapply fiber.mk, exact a, reflexivity,
  intro b, intro p,
  exact rel_of_ab_qg_map_eq_one _ p
Defined.

Definition SES_of_subgroup {B : AbGroup} (S : property B) [is_subgroup B S] : SES (ab_subgroup S) B (quotient_ab_group S).
Proof.
  fapply SES.mk,
  exact incl_of_subgroup S,
  exact ab_qg_map S,
  exact is_embedding_incl_of_subgroup S,
  exact is_surjective_ab_qg_map S,
  fapply is_exact.mk,
  intro a, fapply ab_qg_map_eq_one, induction a with b p, exact p,
  intro b p, fapply tr, fapply fiber.mk, fapply sigma.mk b, fapply rel_of_ab_qg_map_eq_one, exact p, reflexivity,
Defined.

Definition SES_of_surjective_map {B C : AbGroup} (g : B ->g C) (Hg : is_surjective g) : SES (ab_Kernel g) B C.
Proof.
  fapply SES.mk,
  exact ab_Kernel_incl g,
  exact g,
  exact is_embedding_ab_kernel_incl g,
  exact Hg,
  fapply is_exact.mk,
  intro a, induction a with a p, exact p,
  intro b p, fapply tr, fapply fiber.mk, fapply sigma.mk, exact b, exact p, reflexivity,
Defined.

Definition SES_of_homomorphism {A B : AbGroup} (f : A ->g B) : SES (ab_Kernel f) A (ab_Image f).
Proof.
  fapply SES.mk,
  exact ab_Kernel_incl f,
  exact image_lift f,
  exact is_embedding_ab_kernel_incl f,
  exact is_surjective_image_lift f,
  fapply is_exact.mk,
  intro a, induction a with a p, fapply subtype_eq, exact p,
  intro a p, fapply tr, fapply fiber.mk, fapply sigma.mk, exact a,
  exact calc
  f a = image_incl f (image_lift f a) : by exact homotopy_of_eq (ap group_fun (image_factor f)) a
  ... = image_incl f 1 : ap (image_incl f) p
  ... = 1 : by exact respect_one (image_incl f),
  reflexivity
Defined.

Definition SES_of_isomorphism_right {B C : AbGroup} (g : B <~>g C) : SES trivial_ab_group B C.
Proof.
  fapply SES.mk,
  exact from_trivial_ab_group B,
  exact g,
  exact is_embedding_from_trivial_ab_group B,
  fapply is_surjective_of_is_equiv,
  fapply is_exact.mk,
  intro a, induction a, fapply respect_one,
  intro b p,
  have q : g b = g 1,
  from p @ (respect_one g)^-1,
  note r . inj (equiv_of_isomorphism g) q,
  fapply tr, fapply fiber.mk, exact unit.star, rewrite r,
Defined.

structure hom_SES {A B C A' B' C' : AbGroup} (ses : SES A B C) (ses' : SES A' B' C').
  ( hA : A ->g A')
  ( hB : B ->g B')
  ( hC : C ->g C')
  ( htpy1 : hB og (SES.f ses) == (SES.f ses') og hA)
  ( htpy2 : hC og (SES.g ses) == (SES.g ses') og hB)

section ses
parameters {A B C : AbGroup} (ses : SES A B C)

  local abbreviation f . SES.f ses
  local notation `g` . SES.g ses
  local abbreviation ex . SES.ex ses
  local abbreviation q . ab_qg_map (kernel g)
  local abbreviation B_mod_A . quotient_ab_group (kernel g)

Definition SES_iso_stable {A' B' C' : AbGroup} (f' : A' ->g B') (g' : B' ->g C') (α : A' <~>g A) (β : B' <~>g B) (γ : C' <~>g C) (Hαβ : f og α == β og f') (Hβγ : g og β == γ og g') : SES A' B' C'.
Proof.
  fapply SES.mk,
  exact f',
  exact g',
  fapply is_embedding_of_is_injective,
  intros x y p,
  have path : f (α x) = f (α y), by exact calc
  f (α x) = β (f' x) : Hαβ x
  ... = β (f' y) : ap β p
  ... = f (α y)  : (Hαβ y)^-1,
  have path' : α x = α y, by exact @is_injective_of_is_embedding _ _ f (SES.Hf ses) _ _ path,
  exact @is_injective_of_is_embedding _ _ α (is_embedding_of_is_equiv α) _ _ path',
  exact sorry,
  exact sorry,
Defined.

Definition SES_of_triangle_left {A' : AbGroup} (α : A' <~>g A) (f' : A' ->g B) (H : forall a' : A', f (α a') = f' a') : SES A' B C.
Proof.
  fapply SES.mk,
  exact f',
  exact g,
  fapply is_embedding_of_is_injective,
  intro x y p,
  fapply inj (equiv_of_isomorphism α),
  fapply @is_injective_of_is_embedding _ _ f (SES.Hf ses) (α x) (α y),
  rewrite [H x], rewrite [H y], exact p,
  exact SES.Hg ses,
  fapply is_exact.mk,
  intro a',
  rewrite [(H a')^-1],
  fapply is_exact.im_in_ker (SES.ex ses),
  intro b p,
  have  t : image' f b, from is_exact.ker_in_im (SES.ex ses) b p,
  unfold image' at t, induction t, fapply tr, induction a with a h, fapply fiber.mk, exact α^-1ᵍ a, rewrite [(H (α^-1ᵍ a))^-1],
  krewrite [right_inv (equiv_of_isomorphism α) a], exact h
Defined.

--Definition quotient_SES {A B C : AbGroup} (ses : SES A B C) :
(*  quotient_ab_group (image_subgroup (SES.f ses)) <~>g C . *)
(*  begin *)
(*    fapply ab_group_first_iso_thm B C (SES.g ses), *)
(*  end *)

(*Definition pre_right_extend_SES (to separate the followingDefinition and replace C with B/A) *)

Definition quotient_codomain_SES : B_mod_A <~>g C.
Proof.
  exact (codomain_surjection_is_quotient g (SES.Hg ses))
Defined.

  local abbreviation α . quotient_codomain_SES

Definition quotient_triangle_SES : α og q == g.
Proof.
  reflexivity
Defined.

Definition quotient_triangle_extend_SES {C': AbGroup} (k : B ->g C') :
  (Σ (h : C ->g C'), h og g == k) <~> (Σ (h' : B_mod_A ->g C'), h' og q == k).
Proof.
  fapply equiv.mk,
  intro pair, induction pair with h H,
  fapply sigma.mk, exact h og α, intro b,
  exact H b,
  fapply adjointify,
  intro pair, induction pair with h' H', fapply sigma.mk,
  exact h' og α^-1ᵍ,
  intro b,
  exact calc
  h' (α^-1ᵍ (g b)) = h' (α^-1ᵍ (α (q b))) : by reflexivity
  ... = h' (q b) : by exact hwhisker_left h' (left_inv α) (q b)
  ... = k b : by exact H' b,
  intro pair, induction pair with h' H', fapply sigma_eq, esimp, fapply homomorphism_eq, fapply hwhisker_left h' (left_inv α),    esimp, fapply is_prop.elimo, fapply pi.is_trunc_pi, intro a, fapply is_trunc_eq,
  intro pair, induction pair with h H, fapply sigma_eq, esimp, fapply homomorphism_eq, fapply hwhisker_left h (right_inv α),
  esimp, fapply is_prop.elimo, fapply pi.is_trunc_pi, intro a, fapply is_trunc_eq,
Defined.

  parameters {A' B' C' : AbGroup}
  (ses' : SES A' B' C')
  (hA : A ->g A') (hB : B ->g B') (htpy1 : hB og f == (SES.f ses') og hA)

  local abbreviation f' . SES.f ses'
  local notation `g'` . SES.g ses'
  local abbreviation ex' . SES.ex ses'
  local abbreviation q' . ab_qg_map (kernel g')
  local abbreviation α' . quotient_codomain_SES

  include htpy1

Definition quotient_extend_unique_SES : is_contr (Σ (hC : C ->g C'), hC og g == g' og hB).
Proof.
  fapply @(is_trunc_equiv_closed_rev _ (quotient_triangle_extend_SES (g' og hB))),
  fapply ab_qg_universal_property,
  intro b, intro K,
  have k : image' f b, from is_exact.ker_in_im ex b K,
  unfold image' at k, induction k, induction a with a p,
  induction p,
  refine (ap g' (htpy1 a)) @ _,
  fapply is_exact.im_in_ker ex' (hA a)
Defined.

(*
  (* We define a group homomorphism B/ker(g) ->g B'/ker(g'), keeping in mind that ker(g)=A and ker(g')=A'. *)
Definition quotient_extend_SES : quotient_ab_group (kernel_subgroup g) ->g quotient_ab_group (kernel_subgroup g').
Proof.
  fapply ab_group_quotient_homomorphism B B' (kernel_subgroup g) (kernel_subgroup g') hB,
  intro b,
  intro K,
  have k : trunctype.carrier (image_subgroup f b), from is_exact.ker_in_im ex b K,
  induction k, induction a with a p,
  rewrite [p^-1],
  rewrite [htpy1 a],
  fapply is_exact.im_in_ker ex' (hA a)
Defined.

  local abbreviation k . quotient_extend_SES

Definition quotient_extend_SES_square : k og (ab_qg_map (kernel_subgroup g)) == (ab_qg_map (kernel_subgroup g')) og hB.
Proof.
  fapply quotient_group_compute
Defined.

Definition right_extend_SES  : C ->g C'.
  α' og k og α^-1ᵍ

local abbreviation hC . right_extend_SES

Definition right_extend_SES_square : hC og g == g' o hB.
Proof.
  exact calc
  hC og g == hC og α og q              : by reflexivity
  ... == α' og k og α^-1ᵍ og α og q : by reflexivity
  ... == α' og k og q              : by exact hwhisker_left (α' og k) (hwhisker_right q (left_inv α))
  ... == α' og q' og hB            : by exact hwhisker_left α' (quotient_extend_SES_square)
  ... == g' og hB                  : by reflexivity
Defined.

local abbreviation htpy2 . right_extend_SES_square

Definition right_extend_SES_unique_map_aux (hC' : C ->g C') (htpy2' : g' og hB == hC' og g) : k og q ==  α'^-1ᵍ og hC' og α og q.
Proof.
  exact calc
  k og q == q' og hB                : by reflexivity
  ... == α'^-1ᵍ og α' og q' og hB    : by exact hwhisker_right (q' og hB) (homotopy.symm (left_inv α'))
  ... == α'^-1ᵍ og g' og hB          : by reflexivity
  ... == α'^-1ᵍ og hC' og g          : by exact hwhisker_left (α'^-1ᵍ) htpy2'
  ... == α'^-1ᵍ og hC' og α og q     : by reflexivity
Defined.

Definition right_extend_SES_unique_map (hC' : C ->g C') (htpy2' : hC' og g == g' og hB) : hC == hC'.
Proof.
  exact calc
  hC == α' og k og α^-1ᵍ : by reflexivity
  ... == α' og α'^-1ᵍ og hC' og α og α^-1ᵍ :
  ... == hC' og α og α^-1ᵍ : _
  ... == hC' : _
Defined.

Definition right_extend_hom_SES : hom_SES ses ses'.
Proof.
  fapply hom_SES.mk,
  exact hA,
  exact hB,
  exact hC,
  exact htpy1,
  exact htpy2
Defined.
*)

Defined. ses
