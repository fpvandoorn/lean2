(*
Author: Jeremy Avigad
*)
import homotopy.chain_complex .left_module .exactness ..move_to_lib
open eq pointed sigma fiber equiv is_equiv sigma.ops is_trunc nat trunc
open algebra function
open chain_complex
open succ_str
open left_module

structure module_chain_complex (R : Ring) (N : succ_str) : Type.
(mod : N -> LeftModule R)
(hom : forall (n : N), mod (S n) ->lm mod n)
(is_chain_complex :
  forall (n : N) (x : mod (S (S n))), hom n (hom (S n) x) = 0)

namespace left_module
  variables {R : Ring} {N : succ_str}

Definition mcc_mod [coercion] (C : module_chain_complex R N) (n : N) :
  LeftModule R.
  module_chain_complex.mod C n

Definition mcc_carr [coercion] (C : module_chain_complex R N) (n : N) :
  Type.
  C n

Definition mcc_pcarr [coercion] (C : module_chain_complex R N) (n : N) :
  Set*.
  mcc_mod C n

Definition mcc_hom (C : module_chain_complex R N) {n : N} : C (S n) ->lm C n.
  module_chain_complex.hom C n

Definition mcc_is_chain_complex (C : module_chain_complex R N) (n : N) (x : C (S (S n))) :
  mcc_hom C (mcc_hom C x) = 0.
  module_chain_complex.is_chain_complex C n x

  protectedDefinition to_chain_complex [coercion] (C : module_chain_complex R N) :
  chain_complex N.
  chain_complex.mk
  (fun n => mcc_pcarr C n)
  (fun n => pmap_of_homomorphism (@mcc_hom R N C n))
  (mcc_is_chain_complex C)

  (* maybe we don't even need this? *)
Definition is_exact_at_m (C : module_chain_complex R N) (n : N) : Type.
  is_exact_at C n

Definition is_exact_m (C : module_chain_complex R N) : Type.
  ∀n, is_exact_at_m C n

Defined. left_module

namespace left_module
  variable  {R : Ring}
  variables {A₀ B₀ C₀ : LeftModule R}
  variables (f₀ : A₀ ->lm B₀) (g₀ : B₀ ->lm C₀)

Definition is_short_exact . @algebra.is_short_exact  _ _ C₀ f₀ g₀
Defined. left_module
