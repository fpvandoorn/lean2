(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke, Jeremy Avigad

Constructions with groups
*)

import hit.set_quotient .subgroup ..move_to_lib types.equiv

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod trunc function equiv is_equiv
open property

namespace group
  variables {G G' : Group}
  (H : property G) [is_subgroup G H]
  (N : property G) [is_normal_subgroup G N]
  {g g' h h' k : G}
  (N' : property G') [is_normal_subgroup G' N']
  variables {A B : AbGroup}

  (* Quotient Group *)

Definition homotopy_of_homomorphism_eq {f g : G ->g G'}(p : f = g) : f == g.
  fun x : G  => ap010 group_fun p x

Definition quotient_rel (g h : G) : Prop . g * h^-1 ∈ N

  variable {N}

  (* We prove that quotient_rel is an equivalence relation *)
Definition quotient_rel_refl (g : G) : quotient_rel N g g.
  transport (fun x => N x) !mul.right_inv^-1 (subgroup_one_mem N)

Definition quotient_rel_symm (r : quotient_rel N g h) : quotient_rel N h g.
  transport (fun x => N x) (!mul_inv @ ap (fun x => x * _) !inv_inv)
Proof. apply subgroup_inv_mem r end

Definition quotient_rel_trans (r : quotient_rel N g h) (s : quotient_rel N h k)
  : quotient_rel N g k.
  have H1 : N ((g * h^-1) * (h * k^-1)), from subgroup_mul_mem r s,
  have H2 : (g * h^-1) * (h * k^-1) = g * k^-1, from calc
  (g * h^-1) * (h * k^-1) = ((g * h^-1) * h) * k^-1 : by rewrite [mul.assoc (g * h^-1)]
  ... = g * k^-1               : by rewrite inv_mul_cancel_right,
  show N (g * k^-1), by rewrite [-H2]; exact H1

Definition is_equivalence_quotient_rel : is_equivalence (quotient_rel N).
  is_equivalence.mk quotient_rel_refl
  (fun g h => quotient_rel_symm)
  (fun g h k => quotient_rel_trans)

  (* We prove that quotient_rel respects inverses and multiplication, so *)
  (* it is a congruence relation *)
Definition quotient_rel_resp_inv (r : quotient_rel N g h) : quotient_rel N g^-1 h^-1.
  have H1 : g^-1 * (h * g^-1) * g ∈ N, from
  is_normal_subgroup' g (quotient_rel_symm r),
  have H2 : g^-1 * (h * g^-1) * g = g^-1 * h^-1^-1, from calc
  g^-1 * (h * g^-1) * g = g^-1 * h * g^-1 * g : by rewrite -mul.assoc
  ... = g^-1 * h           : inv_mul_cancel_right
  ... = g^-1 * h^-1^-1       : by rewrite algebra.inv_inv,
  show g^-1 * h^-1^-1 ∈ N, by rewrite [-H2]; exact H1

Definition quotient_rel_resp_mul (r : quotient_rel N g h) (r' : quotient_rel N g' h')
  : quotient_rel N (g * g') (h * h').
  have H1 : g * ((g' * h'^-1) * h^-1) ∈ N, from
  normal_subgroup_insert r' r,
  have H2 : g * ((g' * h'^-1) * h^-1) = (g * g') * (h * h')^-1, from calc
  g * ((g' * h'^-1) * h^-1) = g * (g' * (h'^-1 * h^-1)) : by rewrite [mul.assoc]
  ... = (g * g') * (h'^-1 * h^-1) : mul.assoc
  ... = (g * g') * (h * h')^-1 : by rewrite [mul_inv],
  show N ((g * g') * (h * h')^-1), from transport (fun x => N x) H2 H1

  local attribute is_equivalence_quotient_rel [instance]

  variable (N)

Definition qg : Type . set_quotient (quotient_rel N)

  variable {N}

  local attribute qg [reducible]

Definition quotient_one : qg N . class_of one
Definition quotient_inv : qg N -> qg N.
  quotient_unary_map has_inv.inv (fun g g' r => quotient_rel_resp_inv r)
Definition quotient_mul [unfold 3 4] : qg N -> qg N -> qg N.
  quotient_binary_map has_mul.mul (fun g g' r h h' r' => quotient_rel_resp_mul r r')

  section
  local notation 1 . quotient_one
  local postfix ^-1 . quotient_inv
  local infix * . quotient_mul

Definition quotient_mul_assoc (g₁ g₂ g₃ : qg N) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃).
Proof.
  refine set_quotient.rec_prop _ g₁,
  refine set_quotient.rec_prop _ g₂,
  refine set_quotient.rec_prop _ g₃,
  clear g₁ g₂ g₃, intro g₁ g₂ g₃,
  exact ap class_of !mul.assoc
Defined.

Definition quotient_one_mul (g : qg N) : 1 * g = g.
Proof.
  refine set_quotient.rec_prop _ g, clear g, intro g,
  exact ap class_of !one_mul
Defined.

Definition quotient_mul_one (g : qg N) : g * 1 = g.
Proof.
  refine set_quotient.rec_prop _ g, clear g, intro g,
  exact ap class_of !mul_one
Defined.

Definition quotient_mul_left_inv (g : qg N) : g^-1 * g = 1.
Proof.
  refine set_quotient.rec_prop _ g, clear g, intro g,
  exact ap class_of !mul.left_inv
Defined.

Definition quotient_mul_comm {G : AbGroup} {N : property G} [is_normal_subgroup G N] (g h : qg N)
  : g * h = h * g.
Proof.
  refine set_quotient.rec_prop _ g, clear g, intro g,
  refine set_quotient.rec_prop _ h, clear h, intro h,
  apply ap class_of, esimp, apply mul.comm
Defined.

Defined.

  variable (N)
Definition group_qg : group (qg N).
  group.mk _ quotient_mul quotient_mul_assoc quotient_one quotient_one_mul quotient_mul_one
  quotient_inv quotient_mul_left_inv

Definition quotient_group : Group.
  Group.mk _ (group_qg N)

Definition ab_group_qg {G : AbGroup} (N : property G) [is_normal_subgroup G N]
  : ab_group (qg N).
  (ab_group, group_qg N, mul_comm . quotient_mul_comm)

Definition quotient_ab_group {G : AbGroup} (N : property G) [is_subgroup G N]
  : AbGroup.
  AbGroup.mk _ (@ab_group_qg G N (is_normal_subgroup_ab _))

Definition qg_map : G ->g quotient_group N.
  homomorphism.mk class_of (fun g h => idp)

Definition ab_qg_map {G : AbGroup} (N : property G) [is_subgroup G N] : G ->g quotient_ab_group N.
  @qg_map _ N (is_normal_subgroup_ab _)

Definition is_surjective_qg_map {A : Group} (N : property A) [is_normal_subgroup A N] :
  is_surjective (qg_map N).
Proof.
  intro x, induction x,
  fapply image.mk,
  exact a, reflexivity,
  apply is_prop.elimo
Defined.

Definition is_surjective_ab_qg_map {A : AbGroup} (N : property A) [is_subgroup A N] :
  is_surjective (ab_qg_map N).
  @is_surjective_qg_map _ _ _

  namespace quotient
  notation `⟦`:max a `⟧`:0 . qg_map _ a
Defined. quotient

  open quotient
  variables {N N'}

Definition qg_map_eq_one {A : Group} {K : property A} [is_normal_subgroup A K] (g : A)
  (H : g ∈ K) : qg_map K g = 1.
Proof.
  apply set_quotient.eq_of_rel,
  have e : g * 1^-1 = g,
  from calc
  g * 1^-1 = g * 1 : one_inv
  ...   = g : mul_one,
  exact transport (fun x => K x) e^-1 H
Defined.

Definition ab_qg_map_eq_one {A : AbGroup} {K : property A} [is_subgroup A K] (g : A) (H : g ∈ K) :
  ab_qg_map K g = 1.
  @qg_map_eq_one _ _ _ g H

  -(* there should be a smarter way to do this!! Please have a look, Floris. *)
Definition rel_of_qg_map_eq_one (g : G) (H : qg_map N g = 1) : g ∈ N.
Proof.
  have e : (g * 1^-1 = g),
  from calc
  g * 1^-1 = g * 1 : one_inv
  ...   = g : mul_one,
  rewrite (inverse e),
  apply rel_of_eq _ H
Defined.

Definition rel_of_ab_qg_map_eq_one {K : property A} [is_subgroup A K] (a :A) (H : ab_qg_map K a = 1) : a ∈ K.
Proof.
  have e : (a * 1^-1 = a),
  from calc
  a * 1^-1 = a * 1 : one_inv
  ...   = a : mul_one,
  rewrite (inverse e),
  have is_normal_subgroup A K, from is_normal_subgroup_ab _,
  apply rel_of_eq (quotient_rel K) H
Defined.

Definition quotient_group_elim_fun (f : G ->g G') (H : forall , N g -> f g = 1)
  (g : quotient_group N) : G'.
Proof.
  refine set_quotient.elim f _ g,
  intro g h K,
  apply eq_of_mul_inv_eq_one,
  have e : f (g * h^-1) = f g * (f h)^-1,
  from calc
  f (g * h^-1) = f g * (f h^-1) : to_respect_mul
  ...  = f g * (f h)^-1 : to_respect_inv,
  rewrite (inverse e),
  apply H, exact K
Defined.

Definition quotient_group_elim (f : G ->g G') (H : forall (g), g ∈ N -> f g = 1) : quotient_group N ->g G'.
Proof.
  fapply homomorphism.mk,
  (* define function *)
  { exact quotient_group_elim_fun f H } =>
  { intro g h, induction g using set_quotient.rec_prop with g,
  induction h using set_quotient.rec_prop with h,
  krewrite (inverse (to_respect_mul (qg_map N) g h)),
  unfold qg_map, esimp, exact to_respect_mul f g h }
Defined.

  example {K : property A} [is_subgroup A K] :
  quotient_ab_group K = @quotient_group A K (is_normal_subgroup_ab _) . rfl

Definition quotient_ab_group_elim {K : property A} [is_subgroup A K] (f : A ->g B)
  (H : forall (g), g ∈ K -> f g = 1) : quotient_ab_group K ->g B.
  @quotient_group_elim A B K (is_normal_subgroup_ab _) f H

Definition quotient_group_compute (f : G ->g G') (H : forall (g), N g -> f g = 1) (g : G) :
  quotient_group_elim f H (qg_map N g) = f g.
Proof.
  reflexivity
Defined.

Definition gelim_unique (f : G ->g G') (H : forall (g), g ∈ N -> f g = 1) (k : quotient_group N ->g G')
  : ( k og qg_map N == f ) -> k == quotient_group_elim f H.
Proof.
  intro K cg, induction cg using set_quotient.rec_prop with g,
  exact K g
Defined.

Definition ab_gelim_unique {K : property A} [is_subgroup A K] (f : A ->g B) (H : forall (a :A), a ∈ K -> f a = 1) (k : quotient_ab_group K ->g B)
  : ( k og ab_qg_map K == f) -> k == quotient_ab_group_elim f H.
--@quotient_group_elim A B K (is_normal_subgroup_ab _) f H.
  @gelim_unique _ _ K (is_normal_subgroup_ab _) f H _

Definition qg_universal_property (f : G ->g G') (H : forall (g), N g -> f g = 1)  :
  is_contr (Σ(g : quotient_group N ->g G'), g o qg_map N == f).
Proof.
  fapply is_contr.mk,
  (* give center of contraction *)
  { fapply sigma.mk, exact quotient_group_elim f H, exact quotient_group_compute f H },
  (* give contraction *)
  { intro pair, induction pair with g p, fapply sigma_eq,
  {esimp, apply homomorphism_eq, symmetry, exact gelim_unique f H g p},
  {fapply is_prop.elimo} }
Defined.

Definition ab_qg_universal_property {K : property A} [is_subgroup A K] (f : A ->g B) (H : forall (a :A), K a -> f a = 1) :
  is_contr ((Σ(g : quotient_ab_group K ->g B), g og ab_qg_map K == f) ).
Proof.
  fapply @qg_universal_property _ _ K (is_normal_subgroup_ab _),
  exact H
Defined.

Definition quotient_group_functor_contr {K L : property A} [is_subgroup A K] [is_subgroup A L]
  (H : forall (a : A), K a -> L a) :
  is_contr ((Σ(g : quotient_ab_group K ->g quotient_ab_group L), g og ab_qg_map K == ab_qg_map L) ).
Proof.
  fapply ab_qg_universal_property,
  intro a p,
  fapply ab_qg_map_eq_one,
  exact H a p
Defined.

Definition quotient_group_functor_id {K : property A} [is_subgroup A K] (H : forall , K a -> K a) :
  center' (@quotient_group_functor_contr _ K K _ _ H) = ⟨gid (quotient_ab_group K) => fun x => rfl⟩.
Proof.
  note p . @quotient_group_functor_contr _ K K _ _ H =>
  fapply eq_of_is_contr,
Defined.

  section quotient_group_iso_ua

  set_option pp.universes true

Definition subgroup_rel_eq' {K L : property A} [HK : is_subgroup A K] [HL : is_subgroup A L] (htpy : forall (a : A), K a <~> L a) : K = L.
Proof.
  induction HK with Rone Rmul Rinv, induction HL with Rone' Rmul' Rinv', esimp at *,
  assert q : K = L,
Proof.
  fapply eq_of_homotopy,
  intro a,
  fapply tua,
  exact htpy a,
Defined.,
  induction q,
  assert q : Rone = Rone',
Proof.
  fapply is_prop.elim,
Defined.,
  induction q,
  assert q2 : @Rmul = @Rmul',
Proof.
  fapply is_prop.elim,
Defined.,
  induction q2,
  assert q : @Rinv = @Rinv',
Proof.
  fapply is_prop.elim,
Defined.,
  induction q,
  reflexivity
Defined.

Definition subgroup_rel_eq {K L : property A} [is_subgroup A K] [is_subgroup A L] (K_in_L : forall (a : A), a ∈ K -> a ∈ L) (L_in_K : forall (a : A), a ∈ L -> a ∈ K) : K = L.
Proof.
  have htpy : forall (a : A), K a <~> L a,
Proof.
  intro a,
  exact @equiv_of_is_prop (a ∈ K) (a ∈ L) (K_in_L a) (L_in_K a) _ _,
Defined.,
  exact subgroup_rel_eq' htpy,
Defined.

Definition  eq_of_ab_qg_group' {K L : property A} [HK : is_subgroup A K] [HL : is_subgroup A L] (p : K = L) : quotient_ab_group K = quotient_ab_group L.
Proof.
  revert HK, revert HL, induction p, intros,
  have HK = HL, begin apply @is_prop.elim _ _ HK HL end,
  rewrite this
Defined.

Definition iso_of_eq {B : AbGroup} (p : A = B) : A <~>g B.
Proof.
  induction p, fapply isomorphism.mk, exact gid A, fapply adjointify, exact id, intro a, reflexivity, intro a, reflexivity
Defined.

Definition iso_of_ab_qg_group' {K L : property A} [is_subgroup A K] [is_subgroup A L] (p : K = L) : quotient_ab_group K <~>g quotient_ab_group L.
  iso_of_eq (eq_of_ab_qg_group' p)

(*
Definition htpy_of_ab_qg_group' {K L : property A} [HK : is_subgroup A K] [HL : is_subgroup A L] (p : K = L) : (iso_of_ab_qg_group' p) og ab_qg_map K == ab_qg_map L.
Proof.
  revert HK, revert HL, induction p, intros HK HL, unfold iso_of_ab_qg_group', unfold ab_qg_map
(*    have HK = HL, begin apply @is_prop.elim _ _ HK HL end, *)
(*    rewrite this *)
(*    induction p, reflexivity *)
Defined.
*)

Definition eq_of_ab_qg_group {K L : property A} [is_subgroup A K] [is_subgroup A L] (K_in_L : forall (a : A), K a -> L a) (L_in_K : forall (a : A), L a -> K a) : quotient_ab_group K = quotient_ab_group L.
  eq_of_ab_qg_group' (subgroup_rel_eq K_in_L L_in_K)

Definition iso_of_ab_qg_group {K L : property A} [is_subgroup A K] [is_subgroup A L] (K_in_L : forall (a : A), K a -> L a) (L_in_K : forall (a : A), L a -> K a) : quotient_ab_group K <~>g quotient_ab_group L.
  iso_of_eq (eq_of_ab_qg_group K_in_L L_in_K)

(*
Definition htpy_of_ab_qg_group {K L : property A} [is_subgroup A K] [is_subgroup A L] (K_in_L : forall (a : A), K a -> L a) (L_in_K : forall (a : A), L a -> K a) :  iso_of_ab_qg_group K_in_L L_in_K og ab_qg_map K == ab_qg_map L.
Proof.
  fapply htpy_of_ab_qg_group'
Defined.
*)
Defined. quotient_group_iso_ua

  section quotient_group_iso
  variables {K L : property A} [is_subgroup A K] [is_subgroup A L] (H1 : forall (a : A), K a -> L a) (H2 : forall (a : A), L a -> K a)
  include H1
  include H2

Definition quotient_group_iso_contr_KL_map :
  quotient_ab_group K ->g quotient_ab_group L.
  pr1 (center' (quotient_group_functor_contr H1))

Definition quotient_group_iso_contr_KL_triangle :
  quotient_group_iso_contr_KL_map H1 H2 og ab_qg_map K == ab_qg_map L.
  pr2 (center' (quotient_group_functor_contr H1))

Definition quotient_group_iso_contr_KK :
  is_contr (Σ (g : quotient_ab_group K ->g quotient_ab_group K), g og ab_qg_map K == ab_qg_map K).
  @quotient_group_functor_contr A K K _ _ (fun a => H2 a o H1 a)

Definition quotient_group_iso_contr_LK :
  quotient_ab_group L ->g quotient_ab_group K.
  pr1 (center' (@quotient_group_functor_contr A L K _ _ H2))

Definition quotient_group_iso_contr_LL :
  quotient_ab_group L ->g quotient_ab_group L.
  pr1 (center' (@quotient_group_functor_contr A L L _ _ (fun a => H1 a o H2 a)))

(*
Definition quotient_group_iso : quotient_ab_group K <~>g quotient_ab_group L.
Proof.
  fapply isomorphism.mk,
  exact pr1 (center' (quotient_group_iso_contr_KL H1 H2)),
  fapply adjointify,
  exact quotient_group_iso_contr_LK H1 H2,
  intro x,
  induction x, reflexivity,
Defined.
*)

Definition quotient_group_iso_contr_aux  :
  is_contr (Σ(gh : Σ (g : quotient_ab_group K ->g quotient_ab_group L), g og ab_qg_map K == ab_qg_map L), is_equiv (group_fun (pr1 gh))).
Proof.
  fapply is_trunc_sigma,
  exact quotient_group_functor_contr H1 =>
  intro a, induction a with g h,
  fapply is_contr_of_inhabited_prop,
  fapply adjointify,
  rexact group_fun (pr1 (center' (@quotient_group_functor_contr A L K _ _ H2))) =>
  note htpy . homotopy_of_eq (ap group_fun (ap sigma.pr1 (@quotient_group_functor_id _ L _ (fun a => (H1 a) o (H2 a))))),
  have KK : is_contr ((Σ(g' : quotient_ab_group K ->g quotient_ab_group K), g' og ab_qg_map K == ab_qg_map K) ), from
  quotient_group_functor_contr (fun a => (H2 a) o (H1 a)),
  (* have KK_path : ⟨g, h⟩ = ⟨id, fun a => refl (ab_qg_map K a)⟩, from eq_of_is_contr ⟨g, h⟩ ⟨id, fun a => refl (ab_qg_map K a)⟩, *)
  repeat exact sorry
Defined.
(*
Definition quotient_group_iso_contr {K L : property A} [is_subgroup A K] [is_subgroup A L] (H1 : forall (a : A), K a -> L a) (H2 : forall (a : A), L a -> K a) :
  is_contr (Σ (g : quotient_ab_group K <~>g quotient_ab_group L), g og ab_qg_map K == ab_qg_map L).
Proof.
  refine @is_trunc_equiv_closed (Σ(gh : Σ (g : quotient_ab_group K ->g quotient_ab_group L), g og ab_qg_map K == ab_qg_map L), is_equiv (group_fun (pr1 gh))) (Σ (g : quotient_ab_group K <~>g quotient_ab_group L) => g og ab_qg_map K == ab_qg_map L) -2 _ (quotient_group_iso_contr_aux H1 H2),
  exact calc
  (Σ gh, is_equiv (group_fun gh.1)) <~> Σ (g : quotient_ab_group K ->g quotient_ab_group L) (h : g og ab_qg_map K == ab_qg_map L) => is_equiv (group_fun g) : by exact (sigma_assoc_equiv (fun gh => is_equiv (group_fun gh.1)))^-1
  ... <~> (Σ (g : quotient_ab_group K <~>g quotient_ab_group L), g og ab_qg_map K == ab_qg_map L) : _
Defined.
*)

Defined. quotient_group_iso

Definition quotient_group_functor (φ : G ->g G') (h : forall , g ∈ N -> φ g ∈ N') :
  quotient_group N ->g quotient_group N'.
Proof.
  apply quotient_group_elim (qg_map N' og φ),
  intro g Ng, esimp,
  refine qg_map_eq_one (φ g) (h g Ng)
Defined.

------------------------------------------------
  (* FIRST ISOMORPHISM THEOREM *)
------------------------------------------------

Definition kernel_quotient_extension {A B : AbGroup} (f : A ->g B) : quotient_ab_group (kernel f) ->g B.
Proof.
  apply quotient_ab_group_elim f,
  intro a, intro p, exact p
Defined.

Definition kernel_quotient_extension_triangle {A B : AbGroup} (f : A ->g B) :
  kernel_quotient_extension f o ab_qg_map (kernel f) == f.
Proof.
  intro a, reflexivity
Defined.

Definition is_embedding_kernel_quotient_extension {A B : AbGroup} (f : A ->g B) :
  is_embedding (kernel_quotient_extension f).
Proof.
  fapply is_embedding_of_is_mul_hom,
  intro x,
  note H . is_surjective_ab_qg_map (kernel f) x,
  induction H, induction p,
  intro q,
  apply ab_qg_map_eq_one,
  refine _ @ q,
  symmetry,
  rexact kernel_quotient_extension_triangle f a
Defined.

Definition ab_group_quotient_homomorphism (A B : AbGroup)(K : property A)(L : property B) [is_subgroup A K] [is_subgroup B L] (f : A ->g B)
  (p : forall (a:A), a ∈ K -> f a ∈ L) : quotient_ab_group K ->g quotient_ab_group L.
Proof.
  fapply @quotient_group_elim,
  exact (ab_qg_map L) og f,
  intro a,
  intro k,
  exact @ab_qg_map_eq_one B L _ (f a) (p a k),
Defined.

Definition ab_group_kernel_factor {A B C: AbGroup} (f : A ->g B)(g : A ->g C){i : C ->g B}(H : f = i og g )
  : kernel g ⊆ kernel f.
Proof.
  intro a,
  intro p,
  exact calc
  f a = i (g a)            : homotopy_of_eq (ap group_fun H) a
  ... = i 1                : ap i p
  ... = 1                  : respect_one i
Defined.

Definition  ab_group_triv_kernel_factor {A B C: AbGroup} (f : A ->g B)(g : A ->g C){i : C ->g B}(H : f = i og g ) :
 kernel f ⊆ '{1} -> kernel g ⊆ '{1}.
fun p => subproperty.trans (ab_group_kernel_factor f g H) p

Definition is_embedding_of_kernel_subproperty_one {A B : AbGroup} (f : A ->g B) :
  kernel f ⊆ '{1} -> is_embedding f.
fun p => is_embedding_of_is_mul_hom _
  (take x, assume h : f x = 1,
  show x = 1, from eq_of_mem_singleton (p _ h))

Definition kernel_subproperty_one {A B : AbGroup} (f : A ->g B) :
  is_embedding f -> kernel f ⊆ '{1}.
fun h x hx =>
  have x = 1, from eq_one_of_is_mul_hom hx,
  show x ∈ '{1}, from mem_singleton_of_eq this

Definition ab_group_kernel_equivalent {A B : AbGroup} (C : AbGroup) (f : A ->g B)(g : A ->g C)(i : C ->g B)(H : f = i og g )(K : is_embedding i)
  : forall a:A, a ∈ kernel g ↔ a ∈ kernel f.
exteq_of_subproperty_of_subproperty
  (show kernel g ⊆ kernel f, from ab_group_kernel_factor f g H)
  (show kernel f ⊆ kernel g, from
  take a,
  suppose f a = 1,
  have i (g a) = i 1, from calc
  i (g a) = f a       : (homotopy_of_eq (ap group_fun H) a)^-1
  ... = 1         : this
  ... = i 1       : (respect_one i)^-1,
  is_injective_of_is_embedding this)

Definition ab_group_kernel_image_lift (A B : AbGroup) (f : A ->g B)
  : forall a : A, a ∈ kernel (image_lift f) ↔ a ∈ kernel f.
Proof.
  fapply ab_group_kernel_equivalent (ab_Image f) (f) (image_lift(f)) (image_incl(f)),
  exact image_factor f,
  exact is_embedding_of_is_injective (image_incl_injective(f)),
Defined.

Definition ab_group_kernel_quotient_to_image {A B : AbGroup} (f : A ->g B)
  : quotient_ab_group (kernel f) ->g ab_Image (f).
Proof.
  fapply quotient_ab_group_elim (image_lift f), intro a, intro p,
  apply iff.mpr (ab_group_kernel_image_lift _ _ f a) p
Defined.

Definition ab_group_kernel_quotient_to_image_domain_triangle {A B : AbGroup} (f : A ->g B)
  :  ab_group_kernel_quotient_to_image (f) og ab_qg_map (kernel f) == image_lift(f).
Proof.
  intros a,
  esimp,
Defined.

Definition ab_group_kernel_quotient_to_image_codomain_triangle {A B : AbGroup} (f : A ->g B)
  : image_incl f og ab_group_kernel_quotient_to_image f == kernel_quotient_extension f.
Proof.
  intro x,
  induction x,
  reflexivity,
  fapply is_prop.elimo
Defined.

(* set_option pp.all true *)
(* print algebra._trans_of_Group_of_AbGroup_2 *)
Definition is_surjective_kernel_quotient_to_image {A B : AbGroup} (f : A ->g B)
  : is_surjective (ab_group_kernel_quotient_to_image f).
Proof.
  refine is_surjective_factor (ab_qg_map (kernel f)) (image_lift f) _ _,
  apply @quotient_group_compute _ _ _ (@is_normal_subgroup_ab _ (kernel f) _),
  exact is_surjective_image_lift f
Defined.

Definition is_embedding_kernel_quotient_to_image {A B : AbGroup} (f : A ->g B)
  : is_embedding (ab_group_kernel_quotient_to_image f).
Proof.
  fapply is_embedding_factor (image_incl f) (kernel_quotient_extension f),
  exact ab_group_kernel_quotient_to_image_codomain_triangle f,
  exact is_embedding_kernel_quotient_extension f
Defined.

Definition ab_group_first_iso_thm {A B : AbGroup} (f : A ->g B)
  : quotient_ab_group (kernel f) <~>g ab_Image f.
Proof.
  fapply isomorphism.mk,
  exact ab_group_kernel_quotient_to_image f,
  fapply is_equiv_of_is_surjective_of_is_embedding,
  exact is_embedding_kernel_quotient_to_image f,
  exact is_surjective_kernel_quotient_to_image f
Defined.

Definition codomain_surjection_is_quotient {A B : AbGroup} (f : A ->g B)( H : is_surjective f)
  : quotient_ab_group (kernel f) <~>g B.
Proof.
  exact (ab_group_first_iso_thm f) @g (iso_surjection_ab_image_incl f H)
Defined.

Definition codomain_surjection_is_quotient_triangle {A B : AbGroup} (f : A ->g B)( H : is_surjective f)
  : codomain_surjection_is_quotient (f)(H) og ab_qg_map (kernel f) == f.
Proof.
  intro a,
  esimp
Defined.

(* print iff.mpr *)
  (* set generating normal subgroup *)

  section

  parameters {A₁ : AbGroup} (S : A₁ -> Prop)
  variable {A₂ : AbGroup}

  inductive generating_relation' : A₁ -> Type.
  | rincl : forall {g}, S g -> generating_relation' g
  | rmul  : forall {g h}, generating_relation' g -> generating_relation' h -> generating_relation' (g * h)
  | rinv  : forall {g}, generating_relation' g -> generating_relation' g^-1
  | rone  : generating_relation' 1
  open generating_relation'
Definition generating_relation (g : A₁) : Prop . ∥ generating_relation' g ∥
  local abbreviation R . generating_relation
Definition gr_one : R 1 . tr (rone S)
Definition gr_inv (g : A₁) : R g -> R g^-1.
  trunc_functor -1 rinv
Definition gr_mul (g h : A₁) : R g -> R h -> R (g * h).
  trunc_functor2 rmul

Definition normal_generating_relation [instance] : is_subgroup A₁ generating_relation.
  ( is_subgroup,
  one_mem . gr_one,
  inv_mem . gr_inv,
  mul_mem . gr_mul)

  parameter (A₁)
Definition quotient_ab_group_gen : AbGroup . quotient_ab_group generating_relation

Definition gqg_map : A₁ ->g quotient_ab_group_gen.
  ab_qg_map _

  parameter {A₁}
Definition gqg_eq_of_rel {g h : A₁} (H : S (g * h^-1)) : gqg_map g = gqg_map h.
  eq_of_rel (tr (rincl H))

  (* this one might work if the previous one doesn't (maybe make this the default one?) *)
Definition gqg_eq_of_rel' {g h : A₁} (H : S (g * h^-1)) : class_of g = class_of h :> quotient_ab_group_gen.
  gqg_eq_of_rel H

Definition gqg_elim (f : A₁ ->g A₂) (H : forall (g), S g -> f g = 1)
  : quotient_ab_group_gen ->g A₂.
Proof.
  apply quotient_ab_group_elim f,
  intro g r, induction r with r,
  induction r with g s g h r r' IH1 IH2 g r IH,
  { exact H s },
  { exact !respect_mul @ ap011 mul IH1 IH2 @ !one_mul },
  { exact !respect_inv @ ap inv IH @ !one_inv },
  { apply respect_one }
Defined.

Definition gqg_elim_compute (f : A₁ ->g A₂) (H : forall (g), S g -> f g = 1)
  : gqg_elim f H o gqg_map == f.
Proof.
  intro g, reflexivity
Defined.

Definition gqg_elim_unique (f : A₁ ->g A₂) (H : forall (g), S g -> f g = 1)
  (k : quotient_ab_group_gen ->g A₂) : ( k og gqg_map == f ) -> k == gqg_elim f H.
  !ab_gelim_unique

Defined.

Defined. group

namespace group

  variables {G H K : Group} {R : property G} [is_normal_subgroup G R]
  {S : property H} [is_normal_subgroup H S]
  {T : property K} [is_normal_subgroup K T]

Definition quotient_group_functor_compose (ψ : H ->g K) (φ : G ->g H)
  (hψ : forall g, g ∈ S -> ψ g ∈ T) (hφ : forall g, g ∈ R -> φ g ∈ S) :
  quotient_group_functor ψ hψ og quotient_group_functor φ hφ ~
  quotient_group_functor (ψ og φ) (fun g => proof hψ (φ g) qed o hφ g).
Proof.
  intro g, induction g using set_quotient.rec_prop with g hg, reflexivity
Defined.

Definition quotient_group_functor_gid :
  quotient_group_functor (gid G) (fun g => id) == gid (quotient_group R).
Proof.
  intro g, induction g using set_quotient.rec_prop with g hg, reflexivity
Defined.

Definition quotient_group_functor_homotopy {ψ φ : G ->g H} (hψ : forall , R g -> S (ψ g))
  (hφ : forall g, g ∈ R -> φ g ∈ S) (p : φ == ψ) :
  quotient_group_functor φ hφ == quotient_group_functor ψ hψ.
Proof.
  intro g, induction g using set_quotient.rec_prop with g hg,
  exact ap set_quotient.class_of (p g)
Defined.

Definition quotient_group_isomorphism_quotient_group (φ : G <~>g H)
  (h : forall g, g ∈ R ↔ φ g ∈ S) : quotient_group R <~>g quotient_group S.
Proof.
  refine isomorphism.MK (quotient_group_functor φ (fun g => iff.mp (h g)))
  (quotient_group_functor φ^-1ᵍ (fun g gS => iff.mpr (h _) (transport S (right_inv φ g)^-1 gS))) _ _,
  { refine quotient_group_functor_compose _ _ _ _ @hty
  quotient_group_functor_homotopy _ _ proof right_inv φ qed @hty
  quotient_group_functor_gid } =>
  { refine quotient_group_functor_compose _ _ _ _ @hty
  quotient_group_functor_homotopy _ _ proof left_inv φ qed @hty
  quotient_group_functor_gid }
Defined.

Definition is_equiv_qg_map {G : Group} (H : property G) [is_normal_subgroup G H]
  (H₂ : forall (g), g ∈ H -> g = 1) : is_equiv (qg_map H).
  set_quotient.is_equiv_class_of _ (fun g h r => eq_of_mul_inv_eq_one (H₂ r))

Definition quotient_group_isomorphism {G : Group} (H : property G)
  [is_normal_subgroup G H] (h : forall g, g ∈ H -> g = 1) : quotient_group H <~>g G.
  (isomorphism.mk _ (is_equiv_qg_map H h))^-1ᵍ

Defined. group

namespace group

  variables {G H K : AbGroup} {R : property G} [is_subgroup G R]
  {S : property H} [is_subgroup H S]
  {T : property K} [is_subgroup K T]


Definition quotient_ab_group_functor (φ : G ->g H)
  (h : forall g, g ∈ R -> φ g ∈ S) : quotient_ab_group R ->g quotient_ab_group S.
  @quotient_group_functor G H R (is_normal_subgroup_ab _) S (is_normal_subgroup_ab _) φ h

Definition quotient_ab_group_functor_mul
  (ψ φ : G ->g H) (hψ : forall g, g ∈ R -> ψ g ∈ S) (hφ : forall g, g ∈ R -> φ g ∈ S) :
  homomorphism_mul (quotient_ab_group_functor ψ hψ) (quotient_ab_group_functor φ hφ) ~
  quotient_ab_group_functor (homomorphism_mul ψ φ)
  (fun g hg => is_subgroup.mul_mem (hψ g hg) (hφ g hg)).
Proof.
  intro g, induction g using set_quotient.rec_prop with g hg, reflexivity
Defined.

Definition quotient_ab_group_functor_compose (ψ : H ->g K) (φ : G ->g H)
  (hψ : forall g, g ∈ S -> ψ g ∈ T) (hφ : forall g, g ∈ R -> φ g ∈ S) :
  quotient_ab_group_functor ψ hψ og quotient_ab_group_functor φ hφ ~
  quotient_ab_group_functor (ψ og φ) (fun g => proof hψ (φ g) qed o hφ g).
  @quotient_group_functor_compose G H K R _ S _ T _ ψ φ  hψ hφ

Definition quotient_ab_group_functor_gid :
  quotient_ab_group_functor (gid G) (fun g => id) == gid (quotient_ab_group R).
  @quotient_group_functor_gid G R _

Definition quotient_ab_group_functor_homotopy {ψ φ : G ->g H} (hψ : forall , R g -> S (ψ g))
  (hφ : forall g, g ∈ R -> φ g ∈ S) (p : φ == ψ) :
  quotient_ab_group_functor φ hφ == quotient_ab_group_functor ψ hψ.
  @quotient_group_functor_homotopy G H R _ S _ ψ φ hψ hφ p

Definition is_equiv_ab_qg_map {G : AbGroup} (H : property G) [is_subgroup G H]
  (h : forall (g), g ∈ H -> g = 1) : is_equiv (ab_qg_map H).
  proof @is_equiv_qg_map G H (is_normal_subgroup_ab _) h qed

Definition ab_quotient_group_isomorphism {G : AbGroup} (H : property G)
  [is_subgroup G H] (h : forall g, H g -> g = 1) : quotient_ab_group H <~>g G.
  (isomorphism.mk _ (is_equiv_ab_qg_map H h))^-1ᵍ

Definition quotient_ab_group_isomorphism_quotient_ab_group (φ : G <~>g H)
  (h : forall g, g ∈ R ↔ φ g ∈ S) : quotient_ab_group R <~>g quotient_ab_group S.
  @quotient_group_isomorphism_quotient_group _ _ _ _ _ _ φ h

Defined. group
