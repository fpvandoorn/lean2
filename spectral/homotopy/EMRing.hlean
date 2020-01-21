
import .EM .smash_adjoint ..algebra.ring ..algebra.arrow_group

open algebra eq EM is_equiv equiv is_trunc is_conn pointed trunc susp smash group nat function

namespace EM


Definition EM1product_adj {R : Ring} :
  EM1 (AddGroup_of_Ring R) ->* ppMap (EM1 (AddGroup_of_Ring R)) (EMadd1 (AddAbGroup_of_Ring R) 1).
Proof.
  have is_trunc 1 (ppMap (EM1 (AddGroup_of_Ring R)) (EMadd1 (AddAbGroup_of_Ring R) 1)),
  from is_trunc_pmap_of_is_conn _ _ !is_conn_EM1 _ _ _ (le.refl 2) !is_trunc_EMadd1,
  apply EM1_pmap, fapply inf_homomorphism.mk,
  { intro r, refine pfunext _ _ => exact !loop_EM2^-1ᵉ* o* EM1_functor (ring_right_action r) => },
  { intro r r', exact sorry }
Defined.

Definition EMproduct_map {A B C : AbGroup} (φ : A -> B ->g C) (n m : ℕ) (a : A) :
  EMadd1 B n ->* EMadd1 C n.
Proof.
  fapply EMadd1_functor (φ a) n
Defined.

Definition EM0EMadd1product {A B C : AbGroup} (φ : A ->g B ->gg C) (n : ℕ) :
  A ->* EMadd1 B n ->** EMadd1 C n.
EMadd1_pfunctor B C n o* pmap_of_homomorphism φ

Definition EMadd1product {A B C : AbGroup} (φ : A ->g B ->gg C) (n m : ℕ) :
  EMadd1 A n ->* EMadd1 B m ->** EMadd1 C (m + succ n).
Proof.
  assert H1 : is_trunc n.+1 (EMadd1 B m ->** EMadd1 C (m + succ n)),
  { refine is_trunc_pmap_of_is_conn _ (m.-1) !is_conn_EMadd1 _ _ _ _ !is_trunc_EMadd1,
  exact le_of_eq (trunc_index.of_nat_add_plus_two_of_nat m n)^-1ᵖ },
  apply EMadd1_pmap,
  refine (gloopn_pmap_isomorphism (succ n) _ _)^-1ᵍ⁸ o∞g
  gpmap_loop_homomorphism_right (EMadd1 B m) (loopn_EMadd1_add_of_eq C !succ_add)^-1ᵉ* o∞g
  gloop_pmap_isomorphism _ _ o∞g
  (deloop_isomorphism _)^-1ᵍ⁸ o∞g
  EM_ehomomorphism B C (succ m) o∞g
  inf_homomorphism_of_homomorphism φ
Defined.

Definition EMproduct1 {A B C : AbGroup} (φ : A ->g B ->gg C) (n m : ℕ) :
  EM A n ->* EM B m ->** EM C (m + n).
Proof.
  cases n with n,
  { cases m with m,
  { exact pmap_of_homomorphism2 φ },
  { exact EM0EMadd1product φ m }},
  { cases m with m,
  { exact ppcompose_left (ptransport (EMadd1 C) (zero_add n)^-1) o*
  pmap_swap_map (EM0EMadd1product (homomorphism_swap φ) n) },
  { exact ppcompose_left (ptransport (EMadd1 C) !succ_add^-1) o* EMadd1product φ n m }}
Defined.


Definition EMproduct2 {A B C : AbGroup} (φ : A ->g B ->gg C) (n m : ℕ) :
  EM A n ->* (EM B m ->** EM C (m + n)).
Proof.
  assert H1 : is_trunc n (gpmap_loop' (EM B m) (loop_EM C (m + n))),
  { exact is_trunc_pmap_of_is_conn_nat _ m !is_conn_EM _ _ _ !le.refl !is_trunc_EM },
  apply EM_pmap (gpmap_loop' (EM B m) (loop_EM C (m + n))) n,
  exact sorry

Defined.

Definition EMproduct3' {A B C : AbGroup} (φ : A ->g B ->gg C) (n m : ℕ) :
  gEM A n ->∞g gpmap_loop' (EM B m) (loop_EM C (m + n)).
Proof.
  assert H1 : is_trunc n (gpmap_loop' (EM B m) (loop_EM C (m + n))),
  { exact is_trunc_pmap_of_is_conn_nat _ m !is_conn_EM _ _ _ !le.refl !is_trunc_EM },
 exact sorry
Defined.

Definition EMproduct4 {A B C : AbGroup} (φ : A ->g B ->gg C) (n m : ℕ) :
  gEM A n ->∞g Ωg (EM B m ->** EM C (m + n + 1)).
Proof.
  assert H1 : is_trunc (n+1) (EM B m ->** EM C (m + n + 1)),
  { exact is_trunc_pmap_of_is_conn_nat _ m !is_conn_EM _ _ _ !le.refl !is_trunc_EM },
  apply EM_homomorphism_gloop,
  refine (gloopn_pmap_isomorphism _ _ _)^-1ᵍ⁸ o∞g _ o∞g inf_homomorphism_of_homomorphism φ,

  exact sorry
Defined.

Definition EMproduct5 {A B C : AbGroup} (φ : A ->g B ->gg C) (n m : ℕ) :
  InfGroup_of_deloopable (EM A n) ->∞g InfGroup_of_deloopable (EM B m ->** EM C (m + n)).
Proof.
  assert H1 : is_trunc (n + 1) (deloop (EM B m ->** EM C (m + n))),
  { exact is_trunc_pmap_of_is_conn_nat _ m !is_conn_EM _ _ _ !le.refl !is_trunc_EM },
  refine EM_homomorphism_deloopable _ _ _ _ _,

  exact sorry
Defined.

Definition EMadd1product2 {A B C : AbGroup} (φ : A ->g B ->gg C) (n m : ℕ) :
  gEM A (n+1) ->∞g Ωg[succ n] (EMadd1 B m ->** EMadd1 C m).
Proof.
  assert H1 : is_trunc (n+1) (Ω[n] (EMadd1 B m ->** EMadd1 C m)),
  { apply is_trunc_loopn, exact sorry },
  (* the underlying pointed map is: *)
  exact sorry
Defined.


Defined. EM
