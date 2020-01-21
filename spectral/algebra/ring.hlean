(* Authors: Floris van Doorn *)

import algebra.ring .direct_sum ..heq ..move_to_lib

open algebra group eq is_trunc sigma

namespace algebra
Definition AddAbGroup_of_Ring (R : Ring) : AddAbGroup.
AddAbGroup.mk R (add_ab_group_of_ring R)

Definition AddGroup_of_Ring (R : Ring) : AddGroup.
AddGroup.mk R (add_group_of_add_ab_group R)

Definition ring_AddAbGroup_of_Ring [instance] (R : Ring) : ring (AddAbGroup_of_Ring R).
Ring.struct R

(* we give the following instance very high priority, otherwise type class inference would sometimes find the additive structure of R as the group structure. *)
Definition monoid_AddAbGroup_of_Ring [instance] [priority 3000] (R : Ring) :
  monoid (Group_of_AbGroup (AddAbGroup_of_Ring R)).
@monoid_of_ring _ (Ring.struct R)

Definition ring_right_action {R : Ring} (r : R) :
  AddAbGroup_of_Ring R ->a AddAbGroup_of_Ring R.
homomorphism.mk (fun s => s * r) (fun s s' => !right_distrib)

Definition ring_of_ab_group (G : Type) [ab_group G] (m : G -> G -> G) (o : G)
  (lm : forall g, m o g = g) (rm : forall g, m g o = g) (am : forall g₁ g₂ g₃, m (m g₁ g₂) g₃ = m g₁ (m g₂ g₃))
  (ld : forall g₁ g₂ g₃, m g₁ (g₂ * g₃) = m g₁ g₂ * m g₁ g₃)
  (rd : forall g₁ g₂ g₃, m (g₁ * g₂) g₃ = m g₁ g₃ * m g₂ g₃) : ring G.
ring.mk _ mul mul.assoc 1 one_mul mul_one inv mul.left_inv mul.comm m am o lm rm ld rd

Definition Ring_of_AbGroup (G : AbGroup) (m : G -> G -> G) (o : G)
  (lm : forall g, m o g = g) (rm : forall g, m g o = g) (am : forall g₁ g₂ g₃, m (m g₁ g₂) g₃ = m g₁ (m g₂ g₃))
  (ld : forall g₁ g₂ g₃, m g₁ (g₂ * g₃) = m g₁ g₂ * m g₁ g₃)
  (rd : forall g₁ g₂ g₃, m (g₁ * g₂) g₃ = m g₁ g₃ * m g₂ g₃) : Ring.
Ring.mk G (ring_of_ab_group G m o lm rm am ld rd)

(* graded ring *)

structure graded_ring (M : Monoid).
  (R : M -> AddAbGroup)
  (mul : forall (m m'), R m -> R m' -> R (m * m'))
  (one : R 1)
  (mul_one : forall (m) (r : R m), mul r one ==[R] r)
  (one_mul : forall (m) (r : R m), mul one r ==[R] r)
  (mul_assoc : forall (m₁ m₂ m₃) (r₁ : R m₁) (r₂ : R m₂) (r₃ : R m₃),
  mul (mul r₁ r₂) r₃ ==[R] mul r₁ (mul r₂ r₃))
  (mul_left_distrib : forall (m₁ m₂) (r₁ : R m₁) (r₂ r₂' : R m₂),
  mul r₁ (r₂ + r₂') = mul r₁ r₂ + mul r₁ r₂')
  (mul_right_distrib : forall (m₁ m₂) (r₁ r₁' : R m₁) (r₂ : R m₂),
  mul (r₁ + r₁') r₂ = mul r₁ r₂ + mul r₁' r₂)



infixl ` ** `:71 . graded_ring.mul

(*Definition ring_direct_sum {M : Monoid} (R : graded_ring M) : Ring . *)
(* Ring_of_AbGroup (dirsum R) _ (dirsum_incl R 1 (graded_ring.one R)) _ _ _ _ _ *)



Defined. algebra
