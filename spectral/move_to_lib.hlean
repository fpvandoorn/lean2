
import homotopy.sphere2 homotopy.cofiber homotopy.wedge hit.prop_trunc hit.set_quotient eq2 types.pointed2 algebra.graph algebra.category.functor.equivalence

open eq nat int susp pointed sigma is_equiv equiv fiber algebra trunc pi group
  is_trunc function unit prod bool

universe variable u

Definition AddAbGroup.struct2 [instance] (G : AddAbGroup) :
  add_ab_group (algebra._trans_of_Group_of_AbGroup_2 G).
  AddAbGroup.struct G

namespace eq
  (* move to init.equiv *)

  variables {A₀₀ A₂₀ A₀₂ A₂₂ : Type}
  {f₁₀ : A₀₀ -> A₂₀}
  {f₀₁ : A₀₀ -> A₀₂} {f₂₁ : A₂₀ -> A₂₂}
  {f₁₂ : A₀₂ -> A₂₂}

Definition hhinverse' (f₁₀ : A₀₀ <~> A₂₀) (f₁₂ : A₀₂ <~> A₂₂) (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) :
  hsquare f₁₀^-1ᵉ f₁₂^-1ᵉ f₂₁ f₀₁.
  p^-1ʰᵗʸʰ

Definition hvinverse' (f₀₁ : A₀₀ <~> A₀₂) (f₂₁ : A₂₀ <~> A₂₂) (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) :
  hsquare f₁₂ f₁₀ f₀₁^-1ᵉ f₂₁^-1ᵉ.
  p^-1ʰᵗʸᵛ



Definition transport_lemma {A : Type} {C : A -> Type} {g₁ : A -> A}
  {x y : A} (p : x = y) (f : forall (x), C x -> C (g₁ x)) (z : C x) :
  transport C (ap g₁ p)^-1 (f (transport C p z)) = f z.
  by induction p; reflexivity

Definition transport_lemma2 {A : Type} {C : A -> Type} {g₁ : A -> A}
  {x y : A} (p : x = y) (f : forall (x), C x -> C (g₁ x)) (z : C x) :
  transport C (ap g₁ p) (f z) = f (transport C p z).
  by induction p; reflexivity

  variables {A A' B : Type} {a a₂ a₃ : A} {p p' : a = a₂} {p₂ : a₂ = a₃}
  {a' a₂' a₃' : A'} {b b₂ : B}

Defined. eq open eq

namespace int

Definition maxm2_eq_minus_two {n : ℤ} (H : n < 0) : maxm2 n = -2.
Proof.
  induction exists_eq_neg_succ_of_nat H with n p, cases p, reflexivity
Defined.

Defined. int

namespace nat


Defined. nat


namespace pointed

  open option sum
Definition option_equiv_sum (A : Type) : option A <~> A ⊎ unit.
Proof.
  fapply equiv.MK,
  { intro z, induction z with a,
  { exact inr star },
  { exact inl a } },
  { intro z, induction z with a b,
  { exact some a },
  { exact none } },
  { intro z, induction z with a b,
  { reflexivity },
  { induction b, reflexivity } },
  { intro z, induction z with a, all_goals reflexivity }
Defined.

Definition is_trunc_add_point [instance] (n : ℕ₋₂) (A : Type) [HA : is_trunc (n.+2) A]
  : is_trunc (n.+2) A₊.
Proof.
  apply is_trunc_equiv_closed_rev _ (option_equiv_sum A),
  apply is_trunc_sum
Defined.

Defined. pointed open pointed

namespace trunc
  open trunc_index sigma.ops

Definition apn_ptrunc_functor (n : ℕ₋₂) (k : ℕ) {A B : pType} (f : A ->* B) :
  Ω->[k] (ptrunc_functor (n+k) f) o* (loopn_ptrunc_pequiv n k A)^-1ᵉ* ==*
  (loopn_ptrunc_pequiv n k B)^-1ᵉ* o* ptrunc_functor n (Ω->[k] f).
Proof.
  revert n, induction k with k IH: intro n,
  { reflexivity },
  { exact sorry }
Defined.

Defined. trunc open trunc


namespace sigma
  open sigma.ops



Definition sigma_equiv_of_is_embedding_left_fun {X Y : Type} {P : Y -> Type}
  {f : X -> Y} (H : forall y, P y -> fiber f y) (v : Σy, P y) : Σx, P (f x).
  ⟨fiber.point (H v.1 v.2), transport P (point_eq (H v.1 v.2))^-1 v.2⟩

Definition sigma_equiv_of_is_embedding_left {X Y : Type} {P : Y -> Type}
  (f : X -> Y) (Hf : is_embedding f) (HP : forall x, is_prop (P (f x))) (H : forall y, P y -> fiber f y) :
  (Σy, P y) <~> Σx, P (f x).
Proof.
  apply equiv.MK (sigma_equiv_of_is_embedding_left_fun H) (sigma_functor f (fun a => id)),
  { intro v, induction v with x p, esimp [sigma_equiv_of_is_embedding_left_fun] =>
  fapply sigma_eq, apply @is_injective_of_is_embedding _ _ f, exact point_eq (H (f x) p),
  apply is_prop.elimo },
  { intro v, induction v with y p, esimp, fapply sigma_eq, exact point_eq (H y p),
  apply tr_pathover }
Defined.

Definition sigma_equiv_of_is_embedding_left_contr {X Y : Type} {P : Y -> Type}
  (f : X -> Y) (Hf : is_embedding f) (HP : forall x, is_contr (P (f x))) (H : forall y, P y -> fiber f y) :
  (Σy, P y) <~> X.
  sigma_equiv_of_is_embedding_left f Hf _ H @e sigma_equiv_of_is_contr_right _ _

Defined. sigma open sigma

namespace group

Definition group_homomorphism_of_add_group_homomorphism {G₁ G₂ : AddGroup}
  (φ : G₁ ->a G₂) : G₁ ->g G₂.
  φ









  open option
Definition add_point_AbGroup {X : Type} (G : X -> AbGroup) : X₊ -> AbGroup
  | (some x) . G x
  | none     . trivial_ab_group_lift



Defined. group open group

namespace fiber

(* if we need this: do pfiber_functor_pcompose and so on first *)


Defined. fiber open fiber

namespace function
  variables {A B : Type} {f f' : A -> B}
  open is_conn sigma.ops

Definition homotopy_group_isomorphism_of_is_embedding (n : ℕ) [H : is_succ n] {A B : pType}
  (f : A ->* B) [H2 : is_embedding f] : forall g[n] A <~>g forall g[n] B.
Proof.
  apply isomorphism.mk (homotopy_group_homomorphism n f),
  induction H with n,
  apply is_equiv_of_equiv_of_homotopy
  (ptrunc_pequiv_ptrunc 0 (loopn_pequiv_loopn_of_is_embedding (n+1) f)),
  exact sorry
Defined.

Definition merely_constant_pmap {A B : pType} {f : A ->* B} (H : merely_constant f) (a : A) :
  merely (f a = (point _)).
  tconcat (tconcat (H.2 a) (tinverse (H.2 (point _)))) (tr (point_eq f))

Definition merely_constant_of_is_conn {A B : pType} (f : A ->* B) [is_conn 0 A] :
  merely_constant f.
  ⟨(point _), is_conn.elim -1 _ (tr (point_eq f))⟩

Defined. function open function

namespace is_conn

open unit trunc_index nat is_trunc pointed.ops sigma.ops prod.ops



Defined. is_conn


namespace sphere


Defined. sphere


namespace paths

variables {A : Type} {R : A -> A -> Type} {a₁ a₂ a₃ a₄ : A}

Definition mem_equiv_Exists (l : R a₁ a₂) (p : paths R a₃ a₄) :
  mem l p <~> Exists (fun a a' r => ⟨a₁, a₂, l⟩ = ⟨a, a', r⟩) p.
sorry

Defined. paths
