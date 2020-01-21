(*
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz

Reduced cohomology of spectra and cohomology theories
*)

import ..spectrum.basic ..algebra.arrow_group ..algebra.product_group ..choice
  ..homotopy.fwedge ..homotopy.pushout ..homotopy.EM ..homotopy.wedge

open eq spectrum int trunc pointed EM group algebra circle sphere nat EM.ops equiv susp is_trunc
  function fwedge cofiber bool lift sigma is_equiv choice pushout algebra unit pi is_conn wedge

namespace cohomology
universe variables u u' v w
(* The cohomology of X with coefficients in Y is
  trunc 0 (A ->* Ω[2] (Y (n+2)))
  In the file arrow_group (in algebra) we construct the group structure on this type.
  Equivalently, it's
  forall ₛ[n] (sp_cotensor X Y)
*)
Definition cohomology (X : pType) (Y : spectrum) (n : ℤ) : AbGroup.
AbGroup_trunc_pmap X (Y (n+2))

Definition ordinary_cohomology (X : pType) (G : AbGroup) (n : ℤ) : AbGroup.
cohomology X (EM_spectrum G) n

Definition ordinary_cohomology_Z (X : pType) (n : ℤ) : AbGroup.
ordinary_cohomology X agℤ n

Definition unreduced_cohomology (X : Type) (Y : spectrum) (n : ℤ) : AbGroup.
cohomology X₊ Y n

Definition unreduced_ordinary_cohomology (X : Type) (G : AbGroup) (n : ℤ) : AbGroup.
unreduced_cohomology X (EM_spectrum G) n

Definition unreduced_ordinary_cohomology_Z (X : Type) (n : ℤ) : AbGroup.
unreduced_ordinary_cohomology X agℤ n

Definition parametrized_cohomology {X : pType} (Y : X -> spectrum) (n : ℤ) : AbGroup.
AbGroup_trunc_ppi (fun x => Y x (n+2))

Definition ordinary_parametrized_cohomology {X : pType} (G : X -> AbGroup) (n : ℤ) :
  AbGroup.
parametrized_cohomology (fun x => EM_spectrum (G x)) n

Definition unreduced_parametrized_cohomology {X : Type} (Y : X -> spectrum) (n : ℤ) : AbGroup.
parametrized_cohomology (add_point_spectrum Y) n

Definition unreduced_ordinary_parametrized_cohomology {X : Type} (G : X -> AbGroup)
  (n : ℤ) : AbGroup.
unreduced_parametrized_cohomology (fun x => EM_spectrum (G x)) n

notation `H^` n `[`:0 X:0 `, ` Y:0 `]`:0   . cohomology X Y n
notation `oH^` n `[`:0 X:0 `, ` G:0 `]`:0  . ordinary_cohomology X G n
notation `H^` n `[`:0 X:0 `]`:0            . ordinary_cohomology_Z X n
notation `uH^` n `[`:0 X:0 `, ` Y:0 `]`:0  . unreduced_cohomology X Y n
notation `uoH^` n `[`:0 X:0 `, ` G:0 `]`:0 . unreduced_ordinary_cohomology X G n
notation `uH^` n `[`:0 X:0 `]`:0           . unreduced_ordinary_cohomology_Z X n
notation `pH^` n `[`:0 binders `, ` r:(scoped Y, parametrized_cohomology Y n) `]`:0 . r
notation `opH^` n `[`:0 binders `, ` r:(scoped G, ordinary_parametrized_cohomology G n) `]`:0 . r
notation `upH^` n `[`:0 binders `, ` r:(scoped Y, unreduced_parametrized_cohomology Y n) `]`:0 . r
notation `uopH^` n `[`:0 binders `, ` r:(scoped G, unreduced_ordinary_parametrized_cohomology G n) `]`:0 . r

(* an alternateDefinition of cohomology *)

Definition parametrized_cohomology_isomorphism_shomotopy_group_spi {X : pType} (Y : X -> spectrum)
  {n m : ℤ} (p : -m = n) : pH^n[(x : X), Y x] <~>g forall ₛ[m] (spi X Y).
Proof.
  apply isomorphism.trans (trunc_ppi_loop_isomorphism (fun x => loops (Y x (n + 2))))^-1ᵍ,
  apply homotopy_group_isomorphism_of_pequiv 0, esimp,
  have q : sub 2 m = n + 2,
  from (int.add_comm (of_nat 2) (-m) @ ap (fun k => k + of_nat 2) p),
  rewrite q, symmetry, apply loop_pppi_pequiv
Defined.

Definition unreduced_parametrized_cohomology_isomorphism_shomotopy_group_supi {X : Type}
  (Y : X -> spectrum) {n m : ℤ} (p : -m = n) : upH^n[(x : X), Y x] <~>g forall ₛ[m] (supi X Y).
Proof.
  refine parametrized_cohomology_isomorphism_shomotopy_group_spi (add_point_spectrum Y) p @g _,
  apply shomotopy_group_isomorphism_of_pequiv, intro k,
  apply pppi_add_point_over
Defined.

Definition cohomology_isomorphism_shomotopy_group_sp_cotensor (X : pType) (Y : spectrum) {n m : ℤ}
  (p : -m = n) : H^n[X, Y] <~>g forall ₛ[m] (sp_cotensor X Y).
Proof.
  refine parametrized_cohomology_isomorphism_shomotopy_group_spi (fun x => Y) p @g _,
  apply shomotopy_group_isomorphism_of_pequiv, intro k,
  apply pppi_pequiv_ppMap
Defined.

Definition unreduced_cohomology_isomorphism_shomotopy_group_sp_ucotensor (X : Type) (Y : spectrum)
  {n m : ℤ} (p : -m = n) : uH^n[X, Y] <~>g forall ₛ[m] (sp_ucotensor X Y).
Proof.
  refine cohomology_isomorphism_shomotopy_group_sp_cotensor X₊ Y p @g _,
  apply shomotopy_group_isomorphism_of_pequiv, intro k, apply ppMap_add_point
Defined.

(* functoriality *)

Definition cohomology_functor {X X' : pType} (f : X' ->* X) (Y : spectrum)
  (n : ℤ) : cohomology X Y n ->g cohomology X' Y n.
Group_trunc_pmap_homomorphism f

notation `H^->` n `[`:0 f:0 `, ` Y:0 `]`:0   . cohomology_functor f Y n

Definition cohomology_functor_pid (X : pType) (Y : spectrum) (n : ℤ) (f : H^n[X => Y]) :
  cohomology_functor (pid X) Y n f = f.
!Group_trunc_pmap_pid

Definition cohomology_functor_pcompose {X X' X'' : pType} (f : X' ->* X) (g : X'' ->* X')
  (Y : spectrum) (n : ℤ) (h : H^n[X, Y]) : cohomology_functor (f o* g) Y n h =
  cohomology_functor g Y n (cohomology_functor f Y n h).
!Group_trunc_pmap_pcompose

Definition cohomology_functor_phomotopy {X X' : pType} {f g : X' ->* X} (p : f ==* g)
  (Y : spectrum) (n : ℤ) : cohomology_functor f Y n == cohomology_functor g Y n.
Group_trunc_pmap_phomotopy p

notation `H^~` n `[`:0 h:0 `, ` Y:0 `]`:0   . cohomology_functor_phomotopy h Y n

Definition cohomology_functor_phomotopy_refl {X X' : pType} (f : X' ->* X) (Y : spectrum) (n : ℤ)
  (x : H^n[X, Y]) : cohomology_functor_phomotopy (reflexivity f) Y n x = idp.
Group_trunc_pmap_phomotopy_refl f x

Definition cohomology_functor_pconst {X X' : pType} (Y : spectrum) (n : ℤ) (f : H^n[X => Y]) :
  cohomology_functor (pconst X' X) Y n f = 1.
!Group_trunc_pmap_pconst

Definition cohomology_isomorphism {X X' : pType} (f : X' <~>* X) (Y : spectrum) (n : ℤ) :
  H^n[X, Y] <~>g H^n[X', Y].
Group_trunc_pmap_isomorphism f

notation `H^<~>` n `[`:0 e:0 `, ` Y:0 `]`:0 . cohomology_isomorphism e Y n

Definition cohomology_isomorphism_refl (X : pType) (Y : spectrum) (n : ℤ) (x : H^n[X,Y]) :
  H^<~>n[pequiv.refl X, Y] x = x.
!Group_trunc_pmap_isomorphism_refl

Definition cohomology_isomorphism_right (X : pType) {Y Y' : spectrum} (e : forall n, Y n <~>* Y' n)
  (n : ℤ) : H^n[X, Y] <~>g H^n[X, Y'].
cohomology_isomorphism_shomotopy_group_sp_cotensor X Y !neg_neg @g
shomotopy_group_isomorphism_of_pequiv (-n) (fun k => ppMap_pequiv_ppMap_right (e k)) @g
(cohomology_isomorphism_shomotopy_group_sp_cotensor X Y' !neg_neg)^-1ᵍ

Definition unreduced_cohomology_isomorphism {X X' : Type} (f : X' <~> X) (Y : spectrum) (n : ℤ) :
  uH^n[X, Y] <~>g uH^n[X', Y].
cohomology_isomorphism (add_point_pequiv f) Y n

notation `uH^<~>` n `[`:0 e:0 `, ` Y:0 `]`:0 . unreduced_cohomology_isomorphism e Y n

Definition unreduced_cohomology_isomorphism_right (X : Type) {Y Y' : spectrum} (e : forall n, Y n <~>* Y' n)
  (n : ℤ) : uH^n[X, Y] <~>g uH^n[X, Y'].
cohomology_isomorphism_right X₊ e n

Definition unreduced_ordinary_cohomology_isomorphism {X X' : Type} (f : X' <~> X) (G : AbGroup)
  (n : ℤ) : uoH^n[X, G] <~>g uoH^n[X', G].
unreduced_cohomology_isomorphism f (EM_spectrum G) n

notation `uoH^<~>` n `[`:0 e:0 `, ` Y:0 `]`:0 . unreduced_ordinary_cohomology_isomorphism e Y n

Definition unreduced_ordinary_cohomology_isomorphism_right (X : Type) {G G' : AbGroup}
  (e : G <~>g G') (n : ℤ) : uoH^n[X, G] <~>g uoH^n[X, G'].
unreduced_cohomology_isomorphism_right X (EM_spectrum_pequiv e) n

Definition parametrized_cohomology_isomorphism_right {X : pType} {Y Y' : X -> spectrum}
  (e : forall x n, Y x n <~>* Y' x n) (n : ℤ) : pH^n[(x : X), Y x] <~>g pH^n[(x : X), Y' x].
parametrized_cohomology_isomorphism_shomotopy_group_spi Y !neg_neg @g
shomotopy_group_isomorphism_of_pequiv (-n) (fun k => ppi_pequiv_right (fun x => e x k)) @g
(parametrized_cohomology_isomorphism_shomotopy_group_spi Y' !neg_neg)^-1ᵍ

Definition unreduced_parametrized_cohomology_isomorphism_right {X : Type} {Y Y' : X -> spectrum}
  (e : forall x n, Y x n <~>* Y' x n) (n : ℤ) : upH^n[(x : X), Y x] <~>g upH^n[(x : X), Y' x].
parametrized_cohomology_isomorphism_right (fun x' k => add_point_over_pequiv (fun x => e x k) x') n

Definition unreduced_ordinary_parametrized_cohomology_isomorphism_right {X : Type}
  {G G' : X -> AbGroup} (e : forall x, G x <~>g G' x) (n : ℤ) :
  uopH^n[(x : X), G x] <~>g uopH^n[(x : X), G' x].
unreduced_parametrized_cohomology_isomorphism_right (fun x => EM_spectrum_pequiv (e x)) n

Definition ordinary_cohomology_isomorphism_right (X : pType) {G G' : AbGroup} (e : G <~>g G')
  (n : ℤ) : oH^n[X, G] <~>g oH^n[X, G'].
cohomology_isomorphism_right X (EM_spectrum_pequiv e) n

Definition ordinary_parametrized_cohomology_isomorphism_right {X : pType} {G G' : X -> AbGroup}
  (e : forall x, G x <~>g G' x) (n : ℤ) : opH^n[(x : X), G x] <~>g opH^n[(x : X), G' x].
parametrized_cohomology_isomorphism_right (fun x => EM_spectrum_pequiv (e x)) n

Definition uopH_isomorphism_opH {X : Type} (G : X -> AbGroup) (n : ℤ) :
  uopH^n[(x : X), G x] <~>g opH^n[(x : X₊), add_point_AbGroup G x].
parametrized_cohomology_isomorphism_right
Proof.
  intro x n, induction x with x,
  { symmetry, apply EM_spectrum_trivial, },
  { reflexivity }
Defined.
  n

Definition pH_isomorphism_H {X : pType} (Y : spectrum) (n : ℤ) : pH^n[(x : X), Y] <~>g H^n[X, Y].
by reflexivity

Definition opH_isomorphism_oH {X : pType} (G : AbGroup) (n : ℤ) : opH^n[(x : X), G] <~>g oH^n[X, G].
by reflexivity

Definition upH_isomorphism_uH {X : Type} (Y : spectrum) (n : ℤ) : upH^n[(x : X), Y] <~>g uH^n[X, Y].
unreduced_parametrized_cohomology_isomorphism_shomotopy_group_supi _ !neg_neg @g
(unreduced_cohomology_isomorphism_shomotopy_group_sp_ucotensor _ _ !neg_neg)^-1ᵍ

Definition uopH_isomorphism_uoH {X : Type} (G : AbGroup) (n : ℤ) :
  uopH^n[(x : X), G] <~>g uoH^n[X, G].
!upH_isomorphism_uH

Definition uopH_isomorphism_uoH_of_is_conn {X : pType} (G : X -> AbGroup) (n : ℤ) (H : is_conn 1 X) :
  uopH^n[(x : X), G x] <~>g uoH^n[X, G (point _)].
Proof.
  refine _ @g !uopH_isomorphism_uoH,
  apply unreduced_ordinary_parametrized_cohomology_isomorphism_right,
  refine is_conn.elim 0 _ _, reflexivity
Defined.

Definition cohomology_change_int (X : pType) (Y : spectrum) {n n' : ℤ} (p : n = n') :
  H^n[X, Y] <~>g H^n'[X, Y].
isomorphism_of_eq (ap (fun n => H^n[X, Y]) p)

Definition parametrized_cohomology_change_int (X : pType) (Y : X -> spectrum) {n n' : ℤ}
  (p : n = n') : pH^n[(x : X), Y x] <~>g pH^n'[(x : X), Y x].
isomorphism_of_eq (ap (fun n => pH^n[(x : X), Y x]) p)

(* suspension axiom *)

Definition cohomology_susp_2 (Y : spectrum) (n : ℤ) :
  loops (Ω[2] (Y ((n+1)+2))) <~>* Ω[2] (Y (n+2)).
Proof.
  apply loopn_pequiv_loopn 2,
  exact loop_pequiv_loop (pequiv_of_eq (ap Y (add.right_comm n 1 2))) @e* !equiv_glue^-1ᵉ*
Defined.

Definition cohomology_susp_1 (X : pType) (Y : spectrum) (n : ℤ) :
  susp X ->* loops (loops (Y (n + 1 + 2))) <~> X ->* loops (loops (Y (n+2))).
calc
  susp X ->* Ω[2] (Y (n + 1 + 2)) <~> X ->* loops (Ω[2] (Y (n + 1 + 2))) : susp_adjoint_loop_unpointed
  ... <~> X ->* Ω[2] (Y (n+2)) : equiv_of_pequiv (ppMap_pequiv_ppMap_right
  (cohomology_susp_2 Y n))

Definition cohomology_susp_1_pmap_mul {X : pType} {Y : spectrum} {n : ℤ}
  (f g : susp X ->* loops (loops (Y (n + 1 + 2)))) : cohomology_susp_1 X Y n (pmap_mul f g) ==*
  pmap_mul (cohomology_susp_1 X Y n f) (cohomology_susp_1 X Y n g).
Proof.
  unfold [cohomology_susp_1],
  refine pwhisker_left _ !loop_susp_intro_pmap_mul @* _,
  apply pcompose_pmap_mul
Defined.

Definition cohomology_susp_equiv (X : pType) (Y : spectrum) (n : ℤ) :
  H^n+1[susp X, Y] <~> H^n[X, Y].
trunc_equiv_trunc _ (cohomology_susp_1 X Y n)

Definition cohomology_susp (X : pType) (Y : spectrum) (n : ℤ) :
  H^n+1[susp X, Y] <~>g H^n[X, Y].
isomorphism_of_equiv (cohomology_susp_equiv X Y n)
Proof.
  intro f₁ f₂, induction f₁ with f₁, induction f₂ with f₂,
  apply ap tr, apply path_pforall, exact cohomology_susp_1_pmap_mul f₁ f₂
Defined.

Definition cohomology_susp_natural {X X' : pType} (f : X ->* X') (Y : spectrum) (n : ℤ) :
  cohomology_susp X Y n o cohomology_functor (susp_functor f) Y (n+1) ~
  cohomology_functor f Y n o cohomology_susp X' Y n.
Proof.
  refine (trunc_functor_compose _ _ _)^-1ʰᵗʸ @hty _ @hty trunc_functor_compose _ _ _ =>
  apply trunc_functor_homotopy => intro g,
  apply path_pforall, refine _ @* !passoc^-1*, apply pwhisker_left,
  apply loop_susp_intro_natural
Defined.

(* exactness *)

Definition cohomology_exact {X X' : pType} (f : X ->* X') (Y : spectrum) (n : ℤ) :
  is_exact_g (cohomology_functor (pcod f) Y n) (cohomology_functor f Y n).
is_exact_trunc_functor (cofiber_exact f)

(* additivity *)

Definition additive_hom {I : Type} (X : I -> pType) (Y : spectrum) (n : ℤ) :
  H^n[⋁X, Y] ->g forall ᵍ i, H^n[X i, Y].
Group_pi_intro (fun i => cohomology_functor (pinl i) Y n)

Definition additive_equiv {I : Type.{u}} (H : has_choice.{u (max v w)} 0 I) (X : I -> pType.{v})
  (Y : spectrum.{w}) (n : ℤ) : H^n[⋁X, Y] <~> forall ᵍ i, H^n[X i, Y].
trunc_fwedge_pmap_equiv H X (Ω[2] (Y (n+2)))

Definition spectrum_additive {I : Type} (H : has_choice 0 I) (X : I -> pType) (Y : spectrum)
  (n : ℤ) : is_equiv (additive_hom X Y n).
is_equiv_of_equiv_of_homotopy (additive_equiv H X Y n) begin intro f, induction f, reflexivity end

Definition cohomology_fwedge {I : Type.{u}} (H : has_choice 0 I) (X : I -> pType) (Y : spectrum)
  (n : ℤ) : H^n[⋁X, Y] <~>g forall ᵍ i, H^n[X i, Y].
isomorphism.mk (additive_hom X Y n) (spectrum_additive H X Y n)

(* dimension axiom for ordinary cohomology *)
open is_conn trunc_index
Definition ordinary_cohomology_dimension (G : AbGroup) (n : ℤ) (H : n ≠ 0) :
  is_contr (oH^n[pbool, G]).
Proof.
  apply is_conn_equiv_closed 0 !pmap_pbool_equiv^-1ᵉ,
  apply is_conn_equiv_closed 0 !equiv_glue2^-1ᵉ,
  cases n with n n,
  { cases n with n,
  { exfalso, apply H, reflexivity },
  { apply is_conn_of_le, apply zero_le_of_nat n, exact is_conn_EMadd1 G n, }},
  { apply is_trunc_trunc_of_is_trunc, apply @is_contr_loop_of_is_trunc (n+1) (K G 0),
  apply is_trunc_of_le _ (zero_le_of_nat n) _ }
Defined.

Definition ordinary_cohomology_dimension_plift (G : AbGroup) (n : ℤ) (H : n ≠ 0) :
  is_contr (oH^n[plift pbool, G]).
is_trunc_equiv_closed_rev -2
  (equiv_of_isomorphism (cohomology_isomorphism (pequiv_plift pbool) _ _))
  (ordinary_cohomology_dimension G n H)

Definition cohomology_iterate_susp (X : pType) (Y : spectrum) (n : ℤ) (k : ℕ) :
  H^n+k[iterate_susp k X, Y] <~>g H^n[X, Y].
Proof.
  induction k with k IH,
  { exact cohomology_change_int X Y !add_zero },
  { exact cohomology_change_int _ _ !add.assoc^-1 @g cohomology_susp _ _ _ @g IH }
Defined.

Definition ordinary_cohomology_pbool (G : AbGroup) : oH^0[pbool, G] <~>g G.
Proof.
  refine cohomology_isomorphism_shomotopy_group_sp_cotensor _ _ !neg_neg @g _,
  change forall g[2] (pbool ->** EM G 2) <~>g G,
  refine homotopy_group_isomorphism_of_pequiv 1 !ppMap_pbool_pequiv @g ghomotopy_group_EM G 1
Defined.

Definition ordinary_cohomology_sphere (G : AbGroup) (n : ℕ) : oH^n[sphere n, G] <~>g G.
Proof.
  refine cohomology_isomorphism_shomotopy_group_sp_cotensor _ _ !neg_neg @g _,
  change forall g[2] (sphere n ->** EM_spectrum G (2 - -n)) <~>g G,
  refine homotopy_group_isomorphism_of_pequiv 1 _ @g ghomotopy_group_EMadd1 G 1,
  have p : 2 - (-n) = succ (1 + n),
  from !sub_eq_add_neg @ ap (add 2) !neg_neg @ ap of_nat !succ_add,
  refine !sphere_pmap_pequiv @e* Ω<~>[n] (pequiv_ap (EM_spectrum G) p) @e* loopn_EMadd1_add G n 1,
Defined.

Definition ordinary_cohomology_sphere_of_neq (G : AbGroup) {n : ℤ} {k : ℕ} (p : n ≠ k) :
  is_contr (oH^n[sphere k, G]).
Proof.
  refine is_contr_equiv_closed_rev _
  (ordinary_cohomology_dimension G (n-k) (fun h => p (eq_of_sub_eq_zero h))),
  apply equiv_of_isomorphism,
  exact cohomology_change_int _ _ !neg_add_cancel_right^-1 @g
  cohomology_iterate_susp pbool (EM_spectrum G) (n - k) k
Defined.

Definition cohomology_punit (Y : spectrum) (n : ℤ) :
  is_contr (H^n[punit, Y]).
@is_trunc_trunc_of_is_trunc _ _ _ !is_contr_punit_pmap

Definition cohomology_wedge (X : pType.{u}) (X' : pType.{u'}) (Y : spectrum.{v}) (n : ℤ) :
  H^n[wedge X X', Y] <~>g H^n[X, Y] \*ag H^n[X', Y].
H^<~>n[(wedge_pequiv !pequiv_plift !pequiv_plift @e*
  wedge_pequiv_fwedge (plift.{u u'} X) (plift.{u' u} X'))^-1ᵉ*, Y] @g
cohomology_fwedge (has_choice_bool _) _ Y n @g
Group_pi_isomorphism_Group_pi erfl begin intro b, induction b: reflexivity end @g
(product_isomorphism_Group_pi H^n[plift.{u u'} X, Y] H^n[plift.{u' u} X', Y])^-1ᵍ @g
proof H^<~>n[!pequiv_plift, Y] \*<~>g H^<~>n[!pequiv_plift, Y] qed

Definition cohomology_isomorphism_of_equiv {X X' : pType} (e : X <~> X') (Y : spectrum) (n : ℤ) :
  H^n[X', Y] <~>g H^n[X, Y].
!cohomology_susp^-1ᵍ @g H^<~>n+1[susp_pequiv_of_equiv e, Y] @g !cohomology_susp

Definition unreduced_cohomology_split (X : pType.{u}) (Y : spectrum.{v}) (n : ℤ) :
  uH^n[X, Y] <~>g H^n[X, Y] \*ag H^n[pbool, Y].
cohomology_isomorphism_of_equiv (wedge_pbool_equiv_add_point X) Y n @g
cohomology_wedge X pbool Y n

Definition unreduced_ordinary_cohomology_nonzero (X : pType.{u}) (G : AbGroup.{v}) (n : ℤ) (H : n ≠ 0) :
  uoH^n[X, G] <~>g oH^n[X, G].
unreduced_cohomology_split X (EM_spectrum G) n @g
product_trivial_right _ _ (ordinary_cohomology_dimension _ _ H)

Definition unreduced_ordinary_cohomology_zero (X : pType) (G : AbGroup) :
  uoH^0[X, G] <~>g oH^0[X, G] \*ag G.
unreduced_cohomology_split X (EM_spectrum G) 0 @g
(!isomorphism.refl \*<~>g ordinary_cohomology_pbool G)

Definition unreduced_ordinary_cohomology_pbool (G : AbGroup.{v}) : uoH^0[pbool, G] <~>g G \*ag G.
unreduced_ordinary_cohomology_zero pbool G @g (ordinary_cohomology_pbool G \*<~>g !isomorphism.refl)

Definition unreduced_ordinary_cohomology_pbool_nonzero (G : AbGroup) (n : ℤ) (H : n ≠ 0) :
  is_contr (uoH^n[pbool, G]).
is_contr_equiv_closed_rev (equiv_of_isomorphism (unreduced_ordinary_cohomology_nonzero pbool G n H))
  (ordinary_cohomology_dimension G n H)

Definition unreduced_ordinary_cohomology_sphere_zero (G : AbGroup.{u}) (n : ℕ) (H : n ≠ 0) :
  uoH^0[sphere n, G] <~>g G.
unreduced_ordinary_cohomology_zero (sphere n) G @g
product_trivial_left _ _ (ordinary_cohomology_sphere_of_neq _ (fun h => H (of_nat.inj h^-1)))

Definition unreduced_ordinary_cohomology_sphere (G : AbGroup) (n : ℕ) (H : n ≠ 0) :
  uoH^n[sphere n, G] <~>g G.
unreduced_ordinary_cohomology_nonzero (sphere n) G n (fun h => H (of_nat.inj h)) @g
ordinary_cohomology_sphere G n

Definition unreduced_ordinary_cohomology_sphere_of_neq (G : AbGroup) {n : ℤ} {k : ℕ} (p : n ≠ k)
  (q : n ≠ 0) : is_contr (uoH^n[sphere k, G]).
is_contr_equiv_closed_rev
  (equiv_of_isomorphism (unreduced_ordinary_cohomology_nonzero (sphere k) G n q))
  (ordinary_cohomology_sphere_of_neq G p)

Definition unreduced_ordinary_cohomology_sphere_of_neq_nat (G : AbGroup) {n k : ℕ} (p : n ≠ k)
  (q : n ≠ 0) : is_contr (uoH^n[sphere k, G]).
unreduced_ordinary_cohomology_sphere_of_neq G (fun h => p (of_nat.inj h)) (fun h => q (of_nat.inj h))

Definition unreduced_ordinary_cohomology_sphere_of_gt (G : AbGroup) {n k : ℕ} (p : n > k) :
  is_contr (uoH^n[sphere k, G]).
unreduced_ordinary_cohomology_sphere_of_neq_nat
  G (ne_of_gt p) (ne_of_gt (lt_of_le_of_lt (zero_le k) p))

Definition is_contr_cohomology_of_is_contr_spectrum (n : ℤ) (X : pType) (Y : spectrum)
  (H : is_contr (Y n)) : is_contr (H^n[X, Y]).
Proof.
  apply is_trunc_trunc_of_is_trunc,
  apply is_trunc_pmap,
  refine is_contr_equiv_closed_rev _ H,
  exact loop_pequiv_loop (loop_pequiv_loop (pequiv_ap Y (add.assoc n 1 1)^-1) @e* (equiv_glue Y (n+1))^-1ᵉ*) @e
  (equiv_glue Y n)^-1ᵉ*
Defined.

Definition is_contr_ordinary_cohomology (n : ℤ) (X : pType) (G : AbGroup) (H : is_contr G) :
  is_contr (oH^n[X, G]).
Proof.
  apply is_contr_cohomology_of_is_contr_spectrum,
  exact is_contr_EM_spectrum _ _ H
Defined.

Definition is_contr_unreduced_ordinary_cohomology (n : ℤ) (X : Type) (G : AbGroup) (H : is_contr G) :
  is_contr (uoH^n[X, G]).
is_contr_ordinary_cohomology _ _ _ H

Definition is_contr_ordinary_cohomology_of_neg {n : ℤ} (X : pType) (G : AbGroup) (H : n < 0) :
  is_contr (oH^n[X, G]).
Proof.
  apply is_contr_cohomology_of_is_contr_spectrum,
  cases n with n n, contradiction,
  apply is_contr_EM_spectrum_neg
Defined.



(* cohomology theory *)

structure cohomology_theory : Type.
  (HH : ℤ -> pType.{u} -> AbGroup.{u})
  (Hiso : forall (n : ℤ) {X Y : pType} (f : X <~>* Y), HH n Y <~>g HH n X)
  (Hiso_refl : forall (n : ℤ) (X : pType) (x : HH n X), Hiso n pequiv.rfl x = x)
  (Hh : forall (n : ℤ) {X Y : pType} (f : X ->* Y), HH n Y ->g HH n X)
  (Hhomotopy : forall (n : ℤ) {X Y : pType} {f g : X ->* Y} (p : f ==* g), Hh n f == Hh n g)
  (Hhomotopy_refl : forall (n : ℤ) {X Y : pType} (f : X ->* Y) (x : HH n Y),
  Hhomotopy n (reflexivity f) x = idp)
  (Hid : forall (n : ℤ) {X : pType} (x : HH n X), Hh n (pid X) x = x)
  (Hcompose : forall (n : ℤ) {X Y Z : pType} (g : Y ->* Z) (f : X ->* Y) (z : HH n Z),
  Hh n (g o* f) z = Hh n f (Hh n g z))
  (Hsusp : forall (n : ℤ) (X : pType), HH (succ n) (susp X) <~>g HH n X)
  (Hsusp_natural : forall (n : ℤ) {X Y : pType} (f : X ->* Y),
  Hsusp n X o Hh (succ n) (susp_functor f) == Hh n f o Hsusp n Y)
  (Hexact : forall (n : ℤ) {X Y : pType} (f : X ->* Y), is_exact_g (Hh n (pcod f)) (Hh n f))
  (Hadditive : forall (n : ℤ) {I : Type.{u}} (X : I -> pType), has_choice.{u u} 0 I ->
  is_equiv (Group_pi_intro (fun i => Hh n (pinl i)) : HH n (⋁ X) -> forall ᵍ i, HH n (X i)))

structure ordinary_cohomology_theory extends cohomology_theory.{u} : Type.
 (Hdimension : forall (n : ℤ), n ≠ 0 -> is_contr (HH n (plift pbool)))


postfix `^->`:90 . cohomology_theory.Hh
open cohomology_theory

Definition Hequiv (H : cohomology_theory) (n : ℤ) {X Y : pType} (f : X <~>* Y) : H n Y <~> H n X.
equiv_of_isomorphism (Hiso H n f)

Definition Hsusp_neg (H : cohomology_theory) (n : ℤ) (X : pType) : H n (susp X) <~>g H (pred n) X.
isomorphism_of_eq (ap (fun n => H n _) proof (sub_add_cancel n 1)^-1 qed) @g cohomology_theory.Hsusp H (pred n) X

Definition Hsusp_neg_natural (H : cohomology_theory) (n : ℤ) {X Y : pType} (f : X ->* Y) :
  Hsusp_neg H n X o H ^-> n (susp_functor f) == H ^-> (pred n) f o Hsusp_neg H n Y.
sorry

Definition Hsusp_inv_natural (H : cohomology_theory) (n : ℤ) {X Y : pType} (f : X ->* Y) :
  H ^-> (succ n) (susp_functor f) og (Hsusp H n Y)^-1ᵍ == (Hsusp H n X)^-1ᵍ o H ^-> n f.
sorry

Definition Hsusp_neg_inv_natural (H : cohomology_theory) (n : ℤ) {X Y : pType} (f : X ->* Y) :
  H ^-> n (susp_functor f) og (Hsusp_neg H n Y)^-1ᵍ == (Hsusp_neg H n X)^-1ᵍ o H ^-> (pred n) f.
sorry

Definition Hadditive_equiv (H : cohomology_theory) (n : ℤ) {I : Type} (X : I -> pType) (H2 : has_choice 0 I)
  : H n (⋁ X) <~>g forall ᵍ i, H n (X i).
isomorphism.mk _ (Hadditive H n X H2)

Definition Hlift_empty (H : cohomology_theory.{u}) (n : ℤ) :
  is_contr (H n (plift punit)).
let P : lift empty -> pType . lift.rec empty.elim in
let x . Hadditive H n P _ in
Proof.
  note z . equiv.mk _ x,
  refine @(is_trunc_equiv_closed_rev -2 (_ @e z @e _)) !is_contr_unit,
  refine Hequiv H n (pequiv_punit_of_is_contr _ _ @e* !pequiv_plift),
  apply is_contr_fwedge_of_neg, intro y, induction y with y, exact y,
  apply equiv_unit_of_is_contr, apply is_contr_pi_of_neg, intro y, induction y with y, exact y
Defined.

Definition Hempty (H : cohomology_theory.{0}) (n : ℤ) :
  is_contr (H n punit).
@(is_trunc_equiv_closed _ (Hequiv H n !pequiv_plift)) (Hlift_empty H n)

Definition Hconst (H : cohomology_theory) (n : ℤ) {X Y : pType} (y : H n Y) : H ^-> n (pconst X Y) y = 1.
Proof.
  refine Hhomotopy H n (pconst_pcompose (pconst X (plift punit)))^-1* y @ _,
  refine Hcompose H n _ _ y @ _,
  refine ap (H ^-> n _) (@eq_of_is_contr _ (Hlift_empty H n) _ 1) @ _,
  apply respect_one
Defined.


Definition cohomology_theory_spectrum (Y : spectrum.{u}) : cohomology_theory.{u}.
cohomology_theory.mk
  (fun n A => H^n[A, Y])
  (fun n A B f => cohomology_isomorphism f Y n)
  (fun n A => cohomology_isomorphism_refl A Y n)
  (fun n A B f => cohomology_functor f Y n)
  (fun n A B f g p => cohomology_functor_phomotopy p Y n)
  (fun n A B f x => cohomology_functor_phomotopy_refl f Y n x)
  (fun n A x => cohomology_functor_pid A Y n x)
  (fun n A B C g f x => cohomology_functor_pcompose g f Y n x)
  (fun n A => cohomology_susp A Y n)
  (fun n A B f => cohomology_susp_natural f Y n)
  (fun n A B f => cohomology_exact f Y n)
  (fun n I A H => spectrum_additive H A Y n)

Definition ordinary_cohomology_theory_EM (G : AbGroup) : ordinary_cohomology_theory.
(ordinary_cohomology_theory, cohomology_theory_spectrum (EM_spectrum G), Hdimension . ordinary_cohomology_dimension_plift G )

Defined. cohomology
