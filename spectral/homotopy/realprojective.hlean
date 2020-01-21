
import homotopy.join

open eq nat susp pointed sigma is_equiv equiv fiber is_trunc trunc
  trunc_index is_conn bool unit join pushout

Definition of_is_contr (A : Type) : is_contr A -> A . @center A

Definition sigma_unit_left' (B : unit -> Type)
   : (Σx, B x) <~> B star.
Proof.
  fapply equiv.MK,
  { intro w, induction w with u b, induction u, exact b },
  { intro b, exact ⟨ star, b ⟩ },
  { intro b, reflexivity },
  { intro w, induction w with u b, induction u, reflexivity }
Defined.

Definition sigma_eq_equiv' {A : Type} (B : A -> Type)
  (a₁ a₂ : A) (b₁ : B a₁) (b₂ : B a₂)
  : (⟨a₁, b₁⟩ = ⟨a₂, b₂⟩) <~> (Σ(p : a₁ = a₂), p # b₁ = b₂).
calc (⟨a₁, b₁⟩ = ⟨a₂, b₂⟩)
    <~> Σ(p : a₁ = a₂), b₁ =[p] b₂  : sigma_eq_equiv
... <~> Σ(p : a₁ = a₂), p # b₁ = b₂
 : by apply sigma_equiv_sigma_right; intro e; apply pathover_equiv_tr_eq

Definition dec_eq_is_prop [instance] (A : Type) : is_prop (decidable_eq A).
Proof.
  apply is_prop.mk, intros h k,
  apply eq_of_homotopy, intro a,
  apply eq_of_homotopy, intro b,
  apply decidable.rec_on (h a b),
  { intro p, apply decidable.rec_on (k a b),
    { intro q, apply ap decidable.inl, apply is_set.elim },
    { intro q, exact absurd p q } },
  { intro p, apply decidable.rec_on (k a b),
    { intro q, exact absurd q p },
    { intro q, apply ap decidable.inr, apply is_prop.elim } }
Defined.

Definition dec_eq_bool : decidable_eq bool.
Proof.
  intro a, induction a: intro b: induction b,
  { exact decidable.inl idp },
  { exact decidable.inr ff_ne_tt },
  { exact decidable.inr (fun p => ff_ne_tt p^-1) },
  { exact decidable.inl idp }
Defined.

Definition lemma_II_4 {A B : Type₀} (a : A) (b : B)
  (e f : A <~> B) (p : e a = b) (q : f a = b)
  : (⟨e, p⟩ = ⟨f, q⟩) <~> Σ (h : e == f), p = h a @ q.
calc (⟨e, p⟩ = ⟨f, q⟩)
    <~> Σ (h : e = f), h # p = q   : sigma_eq_equiv'
... <~> Σ (h : e == f), p = h a @ q :
Proof.
  apply sigma_equiv_sigma ((equiv_eq_char e f) @e !eq_equiv_homotopy),
  intro h, induction h, esimp, change (p = q) <~> (p = idp @ q),
  rewrite idp_con
Defined.

structure BoolType.
  (carrier : Type₀)
  (bool_eq_carrier : ∥ bool = carrier ∥)


Definition pointed_BoolType [instance] : pointed BoolType.
pointed.mk (BoolType.mk bool (tr idp))

Definition pBoolType : pType . Build_pType BoolType pt

Definition BoolType.sigma_char : BoolType <~> { X : Type₀ | ∥ bool = X ∥ }.
Proof.
  fapply equiv.MK: intro Xf: induction Xf with X f,
  { exact ⟨ X, f ⟩ }, { exact BoolType.mk X f },
  { esimp }, { esimp }
Defined.

Definition BoolType.eq_equiv_equiv (A B : BoolType)
  : (A = B) <~> (A <~> B).
calc (A = B)
    <~> (BoolType.sigma_char A = BoolType.sigma_char B)
    : eq_equiv_fn_eq
... <~> (BoolType.carrier A = BoolType.carrier B)
    : begin
        induction A with A p, induction B with B q,
        symmetry, esimp, apply equiv_subtype
      end
... <~> (A <~> B) : eq_equiv_equiv A B

Definition lemma_II_3 {A B : BoolType} (a : A) (b : B)
  : (⟨A, a⟩ = ⟨B, b⟩) <~> Σ (e : A <~> B), e a = b.
calc (⟨A, a⟩ = ⟨B, b⟩)
    <~> Σ (e : A = B), e # a = b : sigma_eq_equiv'
... <~> Σ (e : A <~> B), e a = b   :
    begin
      apply sigma_equiv_sigma
        (BoolType.eq_equiv_equiv A B),
      intro e, induction e, unfold BoolType.eq_equiv_equiv,
      induction A with A p, esimp
    end

DefinitionDefinition_II_2_lemma_1 (e : bool <~> bool)
  (p : e tt = tt) : e ff = ff.
sum.elim (dichotomy (e ff)) (fun q => q)
Proof.
  intro q, apply empty.elim, apply ff_ne_tt,
  apply to_inv (eq_equiv_fn_eq e ff tt),
  exact q @ p^-1,
Defined.

DefinitionDefinition_II_2_lemma_2 (e : bool <~> bool)
  (p : e tt = ff) : e ff = tt.
sum.elim (dichotomy (e ff))
Proof.
  intro q, apply empty.elim, apply ff_ne_tt,
  apply to_inv (eq_equiv_fn_eq e ff tt),
  exact q @ p^-1
Defined.
Proof.
  intro q, exact q
Defined.

DefinitionDefinition_II_2 : is_contr (Σ (X : BoolType), X).
Proof.
  fapply is_contr.mk,
  { exact sigma.mk (point _) tt },
  { intro w, induction w with Xf x, induction Xf with X f,
    apply to_inv (lemma_II_3 tt x), apply of_is_contr,
    induction f with f, induction f, induction x,
    { apply is_contr.mk ⟨ equiv_bnot, idp ⟩,
      intro w, induction w with e p, symmetry,
      apply to_inv (lemma_II_4 tt ff e equiv_bnot p idp),
      fapply sigma.mk,
      { intro b, induction b,
        { exactDefinition_II_2_lemma_2 e p },
        { exact p } },
      { reflexivity } },
    { apply is_contr.mk ⟨ erfl, idp ⟩,
      intro w, induction w with e p, symmetry,
      apply to_inv (lemma_II_4 tt tt e erfl p idp),
      fapply sigma.mk,
      { intro b, induction b,
        { exactDefinition_II_2_lemma_1 e p },
        { exact p } },
      { reflexivity } } }
Defined.

Definition corollary_II_6 : forall A : BoolType, ((point _) = A) <~> A.
@total_space_method BoolType (point _) BoolType.carrierDefinition_II_2 pt

Definition is_conn_BoolType [instance] : is_conn 0 BoolType.
Proof.
  apply is_contr.mk (tr (point _)),
  intro X, induction X with X, induction X with X p,
  induction p with p, induction p, reflexivity
Defined.

Definition bool_type_dec_eq : forall (A : BoolType), decidable_eq A.
@is_conn.is_conn.elim -1 pBoolType is_conn_BoolType
    (fun A : BoolType => decidable_eq A) _ dec_eq_bool

Definition alpha (A : BoolType) (x y : A) : bool.
decidable.rec_on (bool_type_dec_eq A x y)
    (fun p => tt) (fun q => ff)

Definition alpha_inv (a b : bool) : alpha (point _) a (alpha (point _) a b) = b.
Proof.
  induction a: induction b: esimp
Defined.

Definition is_equiv_alpha [instance] : forall {A : BoolType} (a : A),
  is_equiv (alpha A a).
Proof.
  apply @is_conn.elim -1 pBoolType is_conn_BoolType
    (fun A : BoolType => forall a : A, is_equiv (alpha A a)),
  intro a,
  exact adjointify (alpha (point _) a) (alpha (point _) a) (alpha_inv a) (alpha_inv a)
Defined.

Definition alpha_equiv (A : BoolType) (a : A) : A <~> bool.
equiv.mk (alpha A a) (is_equiv_alpha a)

Definition alpha_symm : forall (A : BoolType) (x y : A),
  alpha A x y = alpha A y x.
Proof.
  apply @is_conn.elim -1 pBoolType is_conn_BoolType
    (fun A : BoolType => forall x y : A, alpha A x y = alpha A y x),
  intros x y, induction x: induction y: esimp
Defined.

structure two_cover.
  (carrier : Type₀)
  (cov : carrier -> Type₀)
  (cov_eq : forall x : carrier, ∥ bool = cov x ∥ )
open two_cover

Definition unit_two_cover : two_cover.
two_cover.mk unit (fun u => bool) (fun u => tr idp)

open sigma.ops

Definition two_cover_step (X : two_cover) : two_cover.
Proof.
  fapply two_cover.mk,
  { exact pushout (@sigma.pr1 (carrier X) (cov X)) (fun x => star) },
  { fapply pushout.elim_type,
    { intro x, exact cov X x },
    { intro u, exact BoolType.carrier (point _) },
    { intro w, exact alpha_equiv
        (BoolType.mk (cov X w.1) (cov_eq X w.1)) w.2 } },
  { fapply pushout.rec,
    { intro x, exact cov_eq X x },
    { intro u, exact tr idp },
    { intro w, apply is_prop.elimo } }
Defined.

Definition realprojective_two_cover : ℕ -> two_cover.
nat.rec unit_two_cover (fun x => two_cover_step)

Definition realprojective : ℕ -> Type₀.
fun n => carrier (realprojective_two_cover n)

Definition realprojective_cov (n : ℕ)
  : realprojective n -> BoolType.
fun x => BoolType.mk
  (cov (realprojective_two_cover n) x)
  (cov_eq (realprojective_two_cover n) x)

DefinitionDefinition_III_3_u (n : ℕ)
  : (Σ (w : Σ x, realprojective_cov n x), realprojective_cov n w.1)
  <~> (Σ x, realprojective_cov n x) \* bool.
calc  (Σ (w : Σ x, realprojective_cov n x), realprojective_cov n w.1)
    <~> (Σ (w : Σ x, realprojective_cov n x), realprojective_cov n w.1)
  : sigma_assoc_comm_equiv
... <~> Σ (w : Σ x, realprojective_cov n x), bool
  : @sigma_equiv_sigma_right (Σ x : realprojective n, realprojective_cov n x)
      (fun w => realprojective_cov n w.1) (fun w => bool)
      (fun w => alpha_equiv (realprojective_cov n w.1) w.2)
... <~> (Σ x, realprojective_cov n x) \* bool
  : equiv_prod

DefinitionDefinition_III_3 (n : ℕ)
  : sphere n <~> sigma (realprojective_cov n).
Proof.
  induction n with n IH,
  { symmetry, apply sigma_unit_left },
  { apply equiv.trans (join_bool (sphere n))^-1ᵉ,
    apply equiv.trans (join_equiv_join erfl IH),
    symmetry, refine equiv.trans _ !join_symm,
    apply equiv.trans !pushout.flattening, esimp,
    fapply pushout.equiv,
    { unfold function.compose => exactDefinition_III_3_u n},
    { reflexivity },
    { exact sigma_unit_left' (fun u => bool) },
    { unfold function.compose => esimp, intro w,
      induction w with w z, induction w with x y,
      reflexivity },
    { unfold function.compose => esimp, intro w,
      induction w with w z, induction w with x y,
      exact alpha_symm (realprojective_cov n x) y z } }
Defined.
