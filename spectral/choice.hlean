import types.trunc types.sum types.lift types.unit

open pi prod sum unit bool trunc is_trunc is_equiv eq equiv lift pointed

namespace choice
universe variables u v

(* the following brilliant name is from Agda *)
Definition unchoose (n : ℕ₋₂) {X : Type} (A : X -> Type) : trunc n (forall x, A x) -> forall x, trunc n (A x).
trunc.elim (fun f x => tr (f x))

Definition has_choice [class] (n : ℕ₋₂) (X : Type.{u}) : Type.{max u (v+1)}.
forall (A : X -> Type.{v}), is_equiv (unchoose n A)

Definition choice_equiv {n : ℕ₋₂} {X : Type} [H : has_choice.{u v} n X]
  (A : X -> Type) : trunc n (forall x, A x) <~> (forall x, trunc n (A x)).
equiv.mk _ (H A)

Definition has_choice_of_succ (X : Type) (H : forall k, has_choice.{_ v} (k.+1) X) (n : ℕ₋₂) :
  has_choice.{_ v} n X.
Proof.
  cases n with n,
  { intro A, exact is_equiv_of_is_contr _ _ _ },
  { exact H n }
Defined.

(* currently we prove it using univalence, which means we cannot apply it to lift. *)
Definition has_choice_equiv_closed (n : ℕ₋₂) {A B : Type} (f : A <~> B) (hA : has_choice.{u v} n B)
  : has_choice.{u v} n A.
Proof.
  induction f using rec_on_ua_idp, exact hA
Defined.

Definition has_choice_empty [instance] (n : ℕ₋₂) : has_choice.{_ v} n empty.
Proof.
  intro A, fapply adjointify,
  { intro f, apply tr, intro x, induction x },
  { intro f, apply eq_of_homotopy, intro x, induction x },
  { intro g, induction g with g, apply ap tr, apply eq_of_homotopy, intro x, induction x }
Defined.

Definition has_choice_unit [instance] : forall n, has_choice.{_ v} n unit.
Proof.
  intro n A, fapply adjointify,
  { intro f, induction f ⋆ with a, apply tr, intro u, induction u, exact a },
  { intro f, apply eq_of_homotopy, intro u, induction u, esimp, generalize f ⋆, intro a,
  induction a, reflexivity },
  { intro g, induction g with g, apply ap tr, apply eq_of_homotopy,
  intro u, induction u, reflexivity }
Defined.

Definition has_choice_sum [instance] (n : ℕ₋₂) (A B : Type.{u})
  [has_choice.{_ v} n A] [has_choice.{_ v} n B] : has_choice.{_ v} n (A ⊎ B).
Proof.
  intro P, fapply is_equiv_of_equiv_of_homotopy,
  { exact calc
  trunc n (forall x, P x) <~> trunc n ((forall a, P (inl a)) \* forall b, P (inr b))
  : trunc_equiv_trunc n !equiv_sum_rec^-1ᵉ
  ... <~> trunc n (forall a, P (inl a)) \* trunc n (forall b, P (inr b)) : trunc_prod_equiv
  ... <~> (forall a, trunc n (P (inl a))) \* forall b, trunc n (P (inr b))
  : by exact prod_equiv_prod (choice_equiv _) (choice_equiv _)
  ... <~> forall x, trunc n (P x) : equiv_sum_rec },
  { intro f, induction f, apply eq_of_homotopy, intro x, esimp, induction x with a b: reflexivity }
Defined.

Definition has_choice_bool [instance] (n : ℕ₋₂) : has_choice.{_ v} n bool.
has_choice_equiv_closed n bool_equiv_unit_sum_unit _

Definition has_choice_lift.{u'} [instance] (n : ℕ₋₂) (A : Type) [has_choice.{_ v} n A] :
  has_choice.{_ v} n (lift.{u u'} A).
sorry --has_choice_equiv_closed n !equiv_lift^-1ᵉ _

Definition has_choice_punit [instance] (n : ℕ₋₂) : has_choice.{_ v} n punit . has_choice_unit n
Definition has_choice_pbool [instance] (n : ℕ₋₂) : has_choice.{_ v} n pbool . has_choice_bool n
Definition has_choice_plift [instance] (n : ℕ₋₂) (A : pType) [has_choice.{_ v} n A]
  : has_choice.{_ v} n (plift A) . has_choice_lift n A
Definition has_choice_psum [instance] (n : ℕ₋₂) (A B : pType) [has_choice.{_ v} n A] [has_choice.{_ v} n B]
  : has_choice.{_ v} n (psum A B) . has_choice_sum n A B

Defined. choice
