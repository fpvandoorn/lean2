import types.trunc types.bool
open eq bool equiv sigma sigma.ops trunc is_trunc pi

namespace choice

  universe variable u

  (* 3.8.1. The axiom of choice. *)
Definition AC . forall (X : Type.{u}) (A : X -> Type.{u}) (P : forall x, A x -> Type.{u}),
  is_set X -> (forall x, is_set (A x)) -> (forall x a, is_prop (P x a)) ->
  (forall x, ∥ Σ a, P x a ∥) -> ∥ Σ f, forall x, P x (f x) ∥

  (* 3.8.3. Corresponds to the assertion that *)
  (* "the cartesian product of a family of nonempty sets is nonempty". *)
Definition AC_cart . forall (X : Type.{u}) (A : X -> Type.{u}),
  is_set X -> (forall x, is_set (A x)) -> (forall x, ∥ A x ∥) -> ∥ forall x, A x ∥

  (* A slight variant of AC with a modified (equivalent) codomain. *)
Definition AC' . forall (X : Type.{u}) (A : X -> Type.{u}) (P : forall x, A x -> Type.{u}),
  is_set X -> (forall x, is_set (A x)) ->  (forall x a, is_prop (P x a))
  -> (forall x, ∥ Σ a, P x a ∥) -> ∥ forall x, Σ a : A x, P x a ∥

  (* The equivalence of AC and AC' follows from the equivalence of their codomains. *)
Definition AC_equiv_AC' : AC.{u} <~> AC'.{u}.
  equiv_of_is_prop
  (fun H X A P HX HA HP HI => trunc_functor _ (to_fun !sigma_pi_equiv_pi_sigma) (H X A P HX HA HP HI))
  (fun H X A P HX HA HP HI => trunc_functor _ (to_inv !sigma_pi_equiv_pi_sigma) (H X A P HX HA HP HI))

  (* AC_cart can be derived from AC' by setting P . fun _ _  => unit. *)
Definition AC_cart_of_AC' : AC'.{u} -> AC_cart.{u}.
  fun H X A HX HA HI => trunc_functor _ (fun H0 x => (H0 x).1)
  (H X A (fun x a => lift.{0 u} unit) HX HA (fun x a => !is_trunc_lift)
  (fun x => trunc_functor _ (fun a => ⟨a, lift.up.{0 u} unit.star⟩) (HI x)))

  (* And the converse, by setting A . fun x => Σ a, P x a. *)
Definition AC'_of_AC_cart : AC_cart.{u} -> AC'.{u}.
  by intro H X A P HX HA HP HI;
  apply H X (fun x => Σ a, P x a) HX (fun x => !is_trunc_sigma) HI

  (* Which is enough to show AC' <~> AC_cart, since both are props. *)
Definition AC'_equiv_AC_cart : AC'.{u} <~> AC_cart.{u}.
  equiv_of_is_prop AC_cart_of_AC'.{u} AC'_of_AC_cart.{u}

  (* 3.8.2. AC <~> AC_cart follows by transitivity. *)
Definition AC_equiv_AC_cart : AC.{u} <~> AC_cart.{u}.
  equiv.trans AC_equiv_AC' AC'_equiv_AC_cart

  namespace example385
Definition X : Type.{1} . Σ A : Type.{0}, ∥ A = bool ∥

Definition x0 : X . ⟨bool, merely.intro _ rfl⟩

Definition Y : X -> Type.{1} . fun x => x0 = x

Definition not_is_set_X : ¬ is_set X.
Proof.
  intro H, apply not_is_prop_bool_eq_bool,
  apply @is_trunc_equiv_closed (x0 = x0),
  apply equiv.symm !equiv_subtype
Defined.

Definition is_set_x1 (x : X) : is_set x.1.
  by cases x; induction a_1; cases a_1; exact _

Definition is_set_Yx (x : X) : is_set (Y x).
Proof.
  apply @is_trunc_equiv_closed _ _ _ !equiv_subtype,
  apply @is_trunc_equiv_closed _ _ _ (equiv.symm !eq_equiv_equiv),
  apply is_trunc_equiv; repeat (apply is_set_x1)
Defined.

Definition trunc_Yx (x : X) : ∥ Y x ∥.
Proof.
  cases x, induction a_1, apply merely.intro,
  apply to_fun !equiv_subtype => rewrite a_1
Defined.

Defined. example385
  open example385

  (* 3.8.5. There exists a type X and a family Y : X -> U such that each Y(x) is a set, *)
  (* but such that (3.8.3) is false. *)
Definition X_must_be_set : Σ (X : Type.{1}) (Y : X -> Type.{1})
  (HA : forall x : X, is_set (Y x)), ¬ ((forall x : X, ∥ Y x ∥) -> ∥ forall x : X, Y x ∥).
  ⟨X, Y, is_set_Yx, fun H => trunc.rec_on (H trunc_Yx)
  (fun H0 => not_is_set_X (@is_trunc_of_is_contr _ _ (is_contr.mk x0 H0)))⟩

Defined. choice
