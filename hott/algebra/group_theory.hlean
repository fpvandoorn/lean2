(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Basic group theory
*)

import algebra.category.category algebra.bundled .homomorphism

open eq algebra pointed function is_trunc pi equiv is_equiv
set_option class.force_new true

namespace group
Definition pointed_Group [instance] (G : Group) : pointed G.
  pointed.mk 1

Definition Group.struct' [instance] (G : Group) : group G.
  Group.struct G

Definition ab_group_pSet_of_Group [instance] (G : AbGroup) : ab_group (pSet_of_Group G).
  AbGroup.struct G

Definition group_pSet_of_Group [instance] [priority 900] (G : Group) :
  group (pSet_of_Group G).
  Group.struct G

  (* left and right actions *)
Definition is_equiv_mul_right {A : Group} (a : A) : is_equiv (fun b => b * a).
  adjointify _ (fun b : A => b * a^-1) (fun b => !inv_mul_cancel_right) (fun b => !mul_inv_cancel_right)

Definition right_action {A : Group} (a : A) : A <~> A.
  equiv.mk _ (is_equiv_mul_right a)

Definition is_equiv_add_right {A : AddGroup} (a : A) : is_equiv (fun b => b + a).
  adjointify _ (fun b : A => b - a) (fun b => !neg_add_cancel_right) (fun b => !add_neg_cancel_right)

Definition add_right_action {A : AddGroup} (a : A) : A <~> A.
  equiv.mk _ (is_equiv_add_right a)

  (* homomorphisms *)

  structure homomorphism (G₁ G₂ : Group) : Type.
  (φ : G₁ -> G₂)
  (p : is_mul_hom φ)

  infix ` ->g `:55 . homomorphism

  abbreviation group_fun [coercion] . @homomorphism.φ
Definition homomorphism.struct [instance] [priority 900] {G₁ G₂ : Group}
  (φ : G₁ ->g G₂) : is_mul_hom φ.
  homomorphism.p φ

Definition homomorphism.mulstruct [instance] [priority 2000] {G₁ G₂ : Group} (φ : G₁ ->g G₂)
  : is_mul_hom φ.
  homomorphism.p φ

Definition homomorphism.addstruct [instance] [priority 2000] {G₁ G₂ : AddGroup} (φ : G₁ ->g G₂)
  : is_add_hom φ.
  homomorphism.p φ

  variables {G G₁ G₂ G₃ : Group} {g h : G₁} {ψ : G₂ ->g G₃} {φ₁ φ₂ : G₁ ->g G₂} (φ : G₁ ->g G₂)

Definition to_respect_mul (* φ *) (g h : G₁) : φ (g * h) = φ g * φ h.
  respect_mul φ g h

Definition to_respect_one (* φ *) : φ 1 = 1.
  respect_one φ

Definition to_respect_inv (* φ *) (g : G₁) : φ g^-1 = (φ g)^-1.
  respect_inv φ g

Definition to_is_embedding_homomorphism (* φ *) (H : forall {g}, φ g = 1 -> g = 1) : is_embedding φ.
  is_embedding_of_is_mul_hom φ @H

  variables (G₁ G₂)
Definition is_set_homomorphism [instance] : is_set (G₁ ->g G₂).
Proof.
  have H : G₁ ->g G₂ <~> Σ(f : G₁ -> G₂), forall (g₁ g₂ : G₁), f (g₁ * g₂) = f g₁ * f g₂,
Proof.
  fapply equiv.MK,
  { intro φ, induction φ, constructor, exact (respect_mul φ)},
  { intro v, induction v with f H, constructor, exact H},
  { intro v, induction v, reflexivity},
  { intro φ, induction φ, reflexivity}
Defined.,
  apply is_trunc_equiv_closed_rev, exact H
Defined.

  variables {G₁ G₂}
Definition pmap_of_homomorphism (* φ *) : G₁ ->* G₂.
  Build_pMap φ begin esimp, exact respect_one φ end

Definition homomorphism_change_fun {G₁ G₂ : Group}
  (φ : G₁ ->g G₂) (f : G₁ -> G₂) (p : φ == f) : G₁ ->g G₂.
  homomorphism.mk f
  (fun g h => (p (g * h))^-1 @ to_respect_mul φ g h @ ap011 mul (p g) (p h))

Definition homomorphism_eq (p : φ₁ == φ₂) : φ₁ = φ₂.
Proof.
  induction φ₁ with φ₁ q₁, induction φ₂ with φ₂ q₂, esimp at p, induction p,
  exact ap (homomorphism.mk φ₁) !is_prop.elim
Defined.

  section additive
  variables {H₁ H₂ : AddGroup} (χ : H₁ ->g H₂)
Definition to_respect_add (* χ *) (g h : H₁) : χ (g + h) = χ g + χ h.
  respect_add χ g h

Definition to_respect_zero (* χ *) : χ 0 = 0.
  respect_zero χ

Definition to_respect_neg (* χ *) (g : H₁) : χ (-g) = -(χ g).
  respect_neg χ g

Defined. additive

  section add_mul
  variables {H₁ : AddGroup} {H₂ : Group} (χ : H₁ ->g H₂)
Definition to_respect_add_mul (* χ *) (g h : H₁) : χ (g + h) = χ g * χ h.
  to_respect_mul χ g h

Definition to_respect_zero_one (* χ *) : χ 0 = 1.
  to_respect_one χ

Definition to_respect_neg_inv (* χ *) (g : H₁) : χ (-g) = (χ g)^-1.
  to_respect_inv χ g

Defined. add_mul

  section mul_add
  variables  {H₁ : Group} {H₂ : AddGroup} (χ : H₁ ->g H₂)
Definition to_respect_mul_add (* χ *) (g h : H₁) : χ (g * h) = χ g + χ h.
  to_respect_mul χ g h

Definition to_respect_one_zero (* χ *) : χ 1 = 0.
  to_respect_one χ

Definition to_respect_inv_neg (* χ *) (g : H₁) : χ g^-1 = -(χ g).
  to_respect_inv χ g

Defined. mul_add

  (* categorical structure of groups + homomorphisms *)

Definition homomorphism_compose [trans] (ψ : G₂ ->g G₃) (φ : G₁ ->g G₂) : G₁ ->g G₃.
  homomorphism.mk (ψ o φ) (is_mul_hom_compose _ _)

  variable (G)
Definition homomorphism_id [refl] : G ->g G.
  homomorphism.mk (@id G) (is_mul_hom_id G)
  variable {G}

  abbreviation gid . @homomorphism_id
  infixr ` og `:75 . homomorphism_compose
  notation 1       . homomorphism_id _

  structure isomorphism (A B : Group).
  (to_hom : A ->g B)
  (is_equiv_to_hom : is_equiv to_hom)

  infix ` <~>g `:25 . isomorphism
  attribute isomorphism.to_hom [coercion]
  attribute isomorphism.is_equiv_to_hom [instance]
  attribute isomorphism._trans_of_to_hom [unfold 3]

Definition equiv_of_isomorphism (φ : G₁ <~>g G₂) : G₁ <~> G₂.
  equiv.mk φ _

Definition pequiv_of_isomorphism (φ : G₁ <~>g G₂) :
  G₁ <~>* G₂.
  pequiv.mk φ begin esimp, exact _ end begin esimp, exact respect_one φ end

Definition isomorphism_of_equiv (φ : G₁ <~> G₂)
  (p : forall g₁ g₂, φ (g₁ * g₂) = φ g₁ * φ g₂) : G₁ <~>g G₂.
  isomorphism.mk (homomorphism.mk φ p) !to_is_equiv

Definition isomorphism_of_eq {G₁ G₂ : Group} (φ : G₁ = G₂) : G₁ <~>g G₂.
  isomorphism_of_equiv (equiv_of_eq (ap Group.carrier φ))
Proof. intros, induction φ, reflexivity end

Definition to_ginv (φ : G₁ <~>g G₂) : G₂ ->g G₁.
  homomorphism.mk φ^-1
  abstract begin
  intro g₁ g₂, apply eq_of_fn_eq_fn' φ,
  rewrite [respect_mul φ, +right_inv φ]
Defined. end

  variable (G)
Definition isomorphism.refl [refl] : G <~>g G.
  isomorphism.mk 1 !is_equiv_id
  variable {G}

Definition isomorphism.symm [symm] (φ : G₁ <~>g G₂) : G₂ <~>g G₁.
  isomorphism.mk (to_ginv φ) !is_equiv_inv

Definition isomorphism.trans [trans] (φ : G₁ <~>g G₂) (ψ : G₂ <~>g G₃) : G₁ <~>g G₃.
  isomorphism.mk (ψ og φ) !is_equiv_compose

Definition isomorphism.eq_trans [trans]
  {G₁ G₂ : Group} {G₃ : Group} (φ : G₁ = G₂) (ψ : G₂ <~>g G₃) : G₁ <~>g G₃.
  proof isomorphism.trans (isomorphism_of_eq φ) ψ qed

Definition isomorphism.trans_eq [trans]
  {G₁ : Group} {G₂ G₃ : Group} (φ : G₁ <~>g G₂) (ψ : G₂ = G₃) : G₁ <~>g G₃.
  isomorphism.trans φ (isomorphism_of_eq ψ)

  postfix `^-1ᵍ`:(max + 1) . isomorphism.symm
  infixl ` @g `:75 . isomorphism.trans
  infixl ` @gp `:75 . isomorphism.trans_eq
  infixl ` @pg `:75 . isomorphism.eq_trans

Definition pmap_of_isomorphism (φ : G₁ <~>g G₂) : G₁ ->* G₂.
  pequiv_of_isomorphism φ

Definition to_fun_isomorphism_trans {G H K : Group} (φ : G <~>g H) (ψ : H <~>g K) :
  φ @g ψ == ψ o φ.
  by reflexivity

Definition add_homomorphism (G H : AddGroup) : Type . homomorphism G H
  infix ` ->a `:55 . add_homomorphism

  abbreviation agroup_fun [coercion] {G H : AddGroup} (φ : G ->a H) : G -> H.
  φ

Definition add_homomorphism.struct [instance] {G H : AddGroup} (φ : G ->a H) : is_add_hom φ.
  homomorphism.addstruct φ

Definition add_homomorphism.mk {G H : AddGroup} (φ : G -> H) (h : is_add_hom φ) : G ->g H.
  homomorphism.mk φ h

Definition add_homomorphism_compose [trans] {G₁ G₂ G₃ : AddGroup}
  (ψ : G₂ ->a G₃) (φ : G₁ ->a G₂) : G₁ ->a G₃.
  add_homomorphism.mk (ψ o φ) (is_add_hom_compose _ _)

Definition add_homomorphism_id [refl] (G : AddGroup) : G ->a G.
  add_homomorphism.mk (@id G) (is_add_hom_id G)

  abbreviation aid . @add_homomorphism_id
  infixr ` oa `:75 . add_homomorphism_compose

Definition to_respect_add' {H₁ H₂ : AddGroup} (χ : H₁ ->a H₂) (g h : H₁) : χ (g + h) = χ g + χ h.
  respect_add χ g h

Definition to_respect_zero' {H₁ H₂ : AddGroup} (χ : H₁ ->a H₂) : χ 0 = 0.
  respect_zero χ

Definition to_respect_neg' {H₁ H₂ : AddGroup} (χ : H₁ ->a H₂) (g : H₁) : χ (-g) = -(χ g).
  respect_neg χ g

Definition homomorphism_add {G H : AddAbGroup} (φ ψ : G ->a H) : G ->a H.
  add_homomorphism.mk (fun g => φ g + ψ g)
  abstract begin
  intro g g', refine ap011 add !to_respect_add' !to_respect_add' @ _,
  refine !add.assoc @ ap (add _) (!add.assoc^-1 @ ap (fun x => x + _) !add.comm @ !add.assoc) @ !add.assoc^-1
Defined. end

Definition homomorphism_mul {G H : AbGroup} (φ ψ : G ->g H) : G ->g H.
  homomorphism.mk (fun g => φ g * ψ g) (to_respect_add (homomorphism_add φ ψ))

Definition pmap_of_homomorphism_gid (G : Group) : pmap_of_homomorphism (gid G) ==* pid G.
Proof.
  fapply phomotopy_of_homotopy, reflexivity
Defined.

Definition pmap_of_homomorphism_gcompose {G H K : Group} (ψ : H ->g K) (φ : G ->g H)
  : pmap_of_homomorphism (ψ og φ) ==* pmap_of_homomorphism ψ o* pmap_of_homomorphism φ.
Proof.
  fapply phomotopy_of_homotopy, reflexivity
Defined.

Definition pmap_of_homomorphism_phomotopy {G H : Group} {φ ψ : G ->g H} (H : φ == ψ)
  : pmap_of_homomorphism φ ==* pmap_of_homomorphism ψ.
Proof.
  fapply phomotopy_of_homotopy, exact H
Defined.

Definition pequiv_of_isomorphism_trans {G₁ G₂ G₃ : Group} (φ : G₁ <~>g G₂) (ψ : G₂ <~>g G₂) :
  pequiv_of_isomorphism (φ @g ψ) ==* pequiv_of_isomorphism ψ o* pequiv_of_isomorphism φ.
Proof.
  apply phomotopy_of_homotopy, reflexivity
Defined.

Definition isomorphism_eq {G H : Group} {φ ψ : G <~>g H} (p : φ == ψ) : φ = ψ.
Proof.
  induction φ with φ φe, induction ψ with ψ ψe,
  exact apd011 isomorphism.mk (homomorphism_eq p) !is_prop.elimo
Defined.

Definition is_set_isomorphism [instance] (G H : Group) : is_set (G <~>g H).
Proof.
  have H : G <~>g H <~> Σ(f : G ->g H), is_equiv f,
Proof.
  fapply equiv.MK,
  { intro φ, induction φ, constructor, assumption },
  { intro v, induction v, constructor, assumption },
  { intro v, induction v, reflexivity },
  { intro φ, induction φ, reflexivity }
Defined.,
  apply is_trunc_equiv_closed_rev, exact H
Defined.

Definition trivial_homomorphism (A B : Group) : A ->g B.
  homomorphism.mk (fun a => 1) (fun a a' => (mul_one 1)^-1)

Definition trivial_add_homomorphism (A B : AddGroup) : A ->a B.
  homomorphism.mk (fun a => 0) (fun a a' => (add_zero 0)^-1)


  (* given an equivalence A <~> B we can transport a group structure on A to a group structure on B *)

  section

  parameters {A B : Type} (f : A <~> B) [group A]

Definition group_equiv_mul (b b' : B) : B . f (f^-1ᶠ b * f^-1ᶠ b')

Definition group_equiv_one : B . f one

Definition group_equiv_inv (b : B) : B . f (f^-1ᶠ b)^-1

  local infix * . group_equiv_mul
  local postfix ^ . group_equiv_inv
  local notation 1 . group_equiv_one

Definition group_equiv_mul_assoc (b₁ b₂ b₃ : B) : (b₁ * b₂) * b₃ = b₁ * (b₂ * b₃).
  by rewrite [↑group_equiv_mul, +left_inv f, mul.assoc]

Definition group_equiv_one_mul (b : B) : 1 * b = b.
  by rewrite [↑group_equiv_mul, ↑group_equiv_one, left_inv f, one_mul, right_inv f]

Definition group_equiv_mul_one (b : B) : b * 1 = b.
  by rewrite [↑group_equiv_mul, ↑group_equiv_one, left_inv f, mul_one, right_inv f]

Definition group_equiv_mul_left_inv (b : B) : b^ * b = 1.
  by rewrite [↑group_equiv_mul, ↑group_equiv_one, ↑group_equiv_inv,
  +left_inv f, mul.left_inv]

Definition group_equiv_closed : group B.
  (group,
  mul          . group_equiv_mul,
  mul_assoc    . group_equiv_mul_assoc,
  one          . group_equiv_one,
  one_mul      . group_equiv_one_mul,
  mul_one      . group_equiv_mul_one,
  inv          . group_equiv_inv,
  mul_left_inv . group_equiv_mul_left_inv,
  is_set_carrier . is_trunc_equiv_closed 0 f)

Defined.

  section
  variables {A B : Type} (f : A <~> B) [ab_group A]
Definition group_equiv_mul_comm (b b' : B) : group_equiv_mul f b b' = group_equiv_mul f b' b.
  by rewrite [↑group_equiv_mul, mul.comm]

Definition ab_group_equiv_closed : ab_group B.
  (ab_group, group_equiv_closed f,
  mul_comm . group_equiv_mul_comm f)
Defined.

  variable (G)

  (* the trivial group *)
  open unit
Definition group_unit : group unit.
  group.mk _ (fun x y => star) (fun x y z => idp) star (unit.rec idp) (unit.rec idp) (fun x => star) (fun x => idp)

Definition ab_group_unit : ab_group unit.
  (ab_group, group_unit, mul_comm . fun x y => idp)

Definition trivial_group : Group.
  Group.mk _ group_unit

  abbreviation G0 . trivial_group

Definition AbGroup_of_Group.{u} (G : Group.{u}) (H : forall x y : G, x * y = y * x) : AbGroup.{u}.
Proof.
  induction G,
  fapply AbGroup.mk,
  assumption,
  exact (ab_group, struct', mul_comm . H)
Defined.

Definition trivial_ab_group : AbGroup.{0}.
Proof.
  fapply AbGroup_of_Group trivial_group, intro x y, reflexivity
Defined.

Definition trivial_group_of_is_contr [H : is_contr G] : G <~>g G0.
Proof.
  fapply isomorphism_of_equiv,
  { apply equiv_unit_of_is_contr},
  { intros, reflexivity}
Defined.

Definition ab_group_of_is_contr (A : Type) [is_contr A] : ab_group A.
  have ab_group unit, from ab_group_unit,
  ab_group_equiv_closed (equiv_unit_of_is_contr A)^-1ᵉ

Definition group_of_is_contr (A : Type) [is_contr A] : group A.
  have ab_group A, from ab_group_of_is_contr A, by apply _

Definition ab_group_lift_unit : ab_group (lift unit).
  ab_group_of_is_contr (lift unit)

Definition trivial_ab_group_lift : AbGroup.
  AbGroup.mk _ ab_group_lift_unit

Definition from_trivial_ab_group (A : AbGroup) : trivial_ab_group ->g A.
  trivial_homomorphism trivial_ab_group A

Definition is_embedding_from_trivial_ab_group (A : AbGroup) :
  is_embedding (from_trivial_ab_group A).
Proof.
  fapply is_embedding_of_is_injective,
  intro x y p,
  induction x, induction y, reflexivity
Defined.

Definition to_trivial_ab_group (A : AbGroup) : A ->g trivial_ab_group.
  trivial_homomorphism A trivial_ab_group

  variable {G}

  (*
  A group where the point in the pointed type corresponds with 1 in the group.
  We need this structure when we are given a pointed type, and want to say that there is a group
  structure on it which is compatible with the point. This is used in chain complexes.
  *)
  structure pgroup [class] (X : pType) extends semigroup X, has_inv X.
  (pt_mul : forall a, mul (point _) a = a)
  (mul_pt : forall a, mul a (point _) = a)
  (mul_left_inv_pt : forall a, mul (inv a) a = (point _))

Definition group_of_pgroup [instance] (X : pType) [H : pgroup X]
  : group X.
  (group, H,
  one . (point _),
  one_mul . pgroup.pt_mul ,
  mul_one . pgroup.mul_pt,
  mul_left_inv . pgroup.mul_left_inv_pt)

Definition pgroup_of_group (X : pType) [H : group X] (p : one = (point _) :> X) : pgroup X.
Proof.
  cases X with X x, esimp at *, induction p,
  exact (pgroup, H,
  pt_mul . one_mul,
  mul_pt . mul_one,
  mul_left_inv_pt . mul.left_inv)
Defined.

Definition Group_of_pgroup (G : pType) [pgroup G] : Group.
  Group.mk G _

Definition pgroup_Group [instance] (G : Group) : pgroup G.
  ( pgroup, Group.struct G,
  pt_mul . one_mul,
  mul_pt . mul_one,
  mul_left_inv_pt . mul.left_inv )

  (* infinity pgroups *)

  structure inf_pgroup [class] (X : pType) extends inf_semigroup X, has_inv X.
  (pt_mul : forall a, mul (point _) a = a)
  (mul_pt : forall a, mul a (point _) = a)
  (mul_left_inv_pt : forall a, mul (inv a) a = (point _))

Definition inf_group_of_inf_pgroup [instance] (X : pType) [H : inf_pgroup X]
  : inf_group X.
  (inf_group, H,
  one . (point _),
  one_mul . inf_pgroup.pt_mul ,
  mul_one . inf_pgroup.mul_pt,
  mul_left_inv . inf_pgroup.mul_left_inv_pt)

Definition inf_pgroup_of_inf_group (X : pType) [H : inf_group X] (p : one = (point _) :> X) : inf_pgroup X.
Proof.
  cases X with X x, esimp at *, induction p,
  exact (inf_pgroup, H,
  pt_mul . one_mul,
  mul_pt . mul_one,
  mul_left_inv_pt . mul.left_inv)
Defined.

Definition inf_Group_of_inf_pgroup (G : pType) [inf_pgroup G] : InfGroup.
  InfGroup.mk G _

Definition inf_pgroup_InfGroup [instance] (G : InfGroup) : inf_pgroup G.
  ( inf_pgroup, InfGroup.struct G,
  pt_mul . one_mul,
  mul_pt . mul_one,
  mul_left_inv_pt . mul.left_inv )

  (* equality of groups and abelian groups *)

Definition group.to_has_mul {A : Type} (H : group A) : has_mul A . _
Definition group.to_has_inv {A : Type} (H : group A) : has_inv A . _
Definition group.to_has_one {A : Type} (H : group A) : has_one A . _
  local attribute group.to_has_mul group.to_has_inv [coercion]

  universe variable l
  variables {A B : Type.{l}}
Definition group_eq {G H : group A} (same_mul' : forall (g h : A), @mul A G g h = @mul A H g h)
  : G = H.
Proof.
  have foo : forall (g : A), @inv A G g = (@inv A G g * g) * @inv A H g,
  from fun g => !mul_inv_cancel_right^-1,
  cases G with Gs Gm Gh1 G1 Gh2 Gh3 Gi Gh4,
  cases H with Hs Hm Hh1 H1 Hh2 Hh3 Hi Hh4,
  have same_mul : Gm = Hm, from eq_of_homotopy2 same_mul',
  cases same_mul,
  have same_one : G1 = H1, from calc
  G1 = Hm G1 H1 : Hh3
  ... = H1 : Gh2,
  have same_inv : Gi = Hi, from eq_of_homotopy (take g, calc
  Gi g = Hm (Hm (Gi g) g) (Hi g) : foo
  ... = Hm G1 (Hi g) : by rewrite Gh4
  ... = Hi g : Gh2),
  cases same_one, cases same_inv,
  have ps  : Gs  = Hs,  from !is_prop.elim,
  have ph1 : Gh1 = Hh1, from !is_prop.elim,
  have ph2 : Gh2 = Hh2, from !is_prop.elim,
  have ph3 : Gh3 = Hh3, from !is_prop.elim,
  have ph4 : Gh4 = Hh4, from !is_prop.elim,
  cases ps, cases ph1, cases ph2, cases ph3, cases ph4, reflexivity
Defined.

Definition group_pathover {G : group A} {H : group B} {p : A = B}
  (resp_mul : forall (g h : A), cast p (g * h) = cast p g * cast p h) : G =[p] H.
Proof.
  induction p,
  apply pathover_idp_of_eq, exact group_eq (resp_mul)
Defined.

Definition Group_eq_of_eq {G H : Group} (p : Group.carrier G = Group.carrier H)
  (resp_mul : forall (g h : G), cast p (g * h) = cast p g * cast p h) : G = H.
Proof.
  cases G with Gc G, cases H with Hc H,
  apply (apd011 Group.mk p),
  exact group_pathover resp_mul
Defined.

Definition Group_eq {G H : Group} (f : Group.carrier G <~> Group.carrier H)
  (resp_mul : forall (g h : G), f (g * h) = f g * f h) : G = H.
  Group_eq_of_eq (ua f) (fun g h => !cast_ua @ resp_mul g h @ ap011 mul !cast_ua^-1 !cast_ua^-1)

Definition eq_of_isomorphism {G₁ G₂ : Group} (φ : G₁ <~>g G₂) : G₁ = G₂.
  Group_eq (equiv_of_isomorphism φ) (respect_mul φ)

Definition ab_group.to_has_mul {A : Type} (H : ab_group A) : has_mul A . _
  local attribute ab_group.to_has_mul [coercion]

Definition ab_group_eq {A : Type} {G H : ab_group A}
  (same_mul : forall (g h : A), @mul A G g h = @mul A H g h)
  : G = H.
Proof.
  have g_eq : @ab_group.to_group A G = @ab_group.to_group A H, from group_eq same_mul,
  cases G with Gs Gm Gh1 G1 Gh2 Gh3 Gi Gh4 Gh5,
  cases H with Hs Hm Hh1 H1 Hh2 Hh3 Hi Hh4 Hh5,
  have pm : Gm = Hm, from ap (@mul _ o group.to_has_mul) g_eq,
  have pi : Gi = Hi, from ap (@inv _ o group.to_has_inv) g_eq,
  have p1 : G1 = H1, from ap (@one _ o group.to_has_one) g_eq,
  induction pm, induction pi, induction p1,
  have ps  : Gs  = Hs,  from !is_prop.elim,
  have ph1 : Gh1 = Hh1, from !is_prop.elim,
  have ph2 : Gh2 = Hh2, from !is_prop.elim,
  have ph3 : Gh3 = Hh3, from !is_prop.elim,
  have ph4 : Gh4 = Hh4, from !is_prop.elim,
  have ph5 : Gh5 = Hh5, from !is_prop.elim,
  induction ps, induction ph1, induction ph2, induction ph3, induction ph4, induction ph5,
  reflexivity
Defined.

Definition ab_group_pathover {A B : Type} {G : ab_group A} {H : ab_group B} {p : A = B}
  (resp_mul : forall (g h : A), cast p (g * h) = cast p g * cast p h) : G =[p] H.
Proof.
  induction p,
  apply pathover_idp_of_eq, exact ab_group_eq (resp_mul)
Defined.

Definition AbGroup_eq_of_isomorphism {G₁ G₂ : AbGroup} (φ : G₁ <~>g G₂) : G₁ = G₂.
Proof.
  induction G₁, induction G₂,
  apply apd011 AbGroup.mk (ua (equiv_of_isomorphism φ)),
  apply ab_group_pathover,
  intro g h, exact !cast_ua @ respect_mul φ g h @ ap011 mul !cast_ua^-1 !cast_ua^-1
Defined.

Definition trivial_group_of_is_contr' (G : Group) [H : is_contr G] : G = G0.
  eq_of_isomorphism (trivial_group_of_is_contr G)


Defined. group
