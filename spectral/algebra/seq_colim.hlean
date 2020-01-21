--Authors: Robert Rose, Liz Vidaurre

import .direct_sum ..move_to_lib

open eq algebra is_trunc set_quotient relation sigma prod sum list trunc function equiv sigma.ops nat

namespace group

  section

  parameters (A : ℕ -> AbGroup) (f : forall i , A i ->g A (i + 1))
  variables {A' : AbGroup}

Definition seq_colim_carrier : AbGroup . dirsum A
  inductive seq_colim_rel : seq_colim_carrier -> Type.
  | rmk : forall i a, seq_colim_rel ((dirsum_incl A i a) * (dirsum_incl A (i + 1) (f i a))^-1)

Definition seq_colim : AbGroup . quotient_ab_group_gen seq_colim_carrier (fun a => ∥seq_colim_rel a∥)

  parameters {A f}
Definition seq_colim_incl (i : ℕ) : A i ->g seq_colim.
  gqg_map _ _ og dirsum_incl A i

Definition seq_colim_quotient (h : forall i, A i ->g A') (k : forall i a, h i a = h (succ i) (f i a))
  (v : seq_colim_carrier) (r : ∥seq_colim_rel v∥) : dirsum_elim h v = 1.
Proof.
  induction r with r, induction r,
  refine !to_respect_mul @ _,
  refine ap (fun γ => group_fun (dirsum_elim h) (group_fun (dirsum_incl A i) a) * group_fun (dirsum_elim h) γ)
  (!to_respect_inv)^-1 @ _,
  refine ap (fun γ => γ * group_fun (dirsum_elim h) (group_fun (dirsum_incl A (succ i)) (f i a)^-1))
  !dirsum_elim_compute @ _,
  refine ap (fun γ => (h i a) * γ) !dirsum_elim_compute @ _,
  refine ap (fun γ => γ * group_fun (h (succ i)) (f i a)^-1) !k @ _ =>
  refine ap (fun γ => group_fun (h (succ i)) (f i a) * γ) (!to_respect_inv) @ _ =>
  exact !mul.right_inv
Defined.

Definition seq_colim_elim (h : forall i, A i ->g A')
  (k : forall i a, h i a = h (succ i) (f i a)) : seq_colim ->g A'.
  gqg_elim _ (dirsum_elim h) (seq_colim_quotient h k)

Definition seq_colim_compute (h : forall i, A i ->g A')
  (k : forall i a, h i a = h (succ i) (f i a)) (i : ℕ) (a : A i) :
  (seq_colim_elim h k) (seq_colim_incl i a) = h i a.
Proof.
  refine gqg_elim_compute (fun a => ∥seq_colim_rel a∥) (dirsum_elim h) (seq_colim_quotient h k) (dirsum_incl A i a) @ _,
  exact !dirsum_elim_compute
Defined.

Definition seq_colim_glue {i : @trunctype.mk 0 ℕ _} {a : A i} : seq_colim_incl i a = seq_colim_incl (succ i) (f i a).
Proof.
  refine gqg_eq_of_rel _ _,
  exact tr (seq_colim_rel.rmk _ _)
Defined.

  section
  local abbreviation h (m : seq_colim ->g A') : forall i, A i ->g A' . fun i => m og (seq_colim_incl i)
  local abbreviation k (m : seq_colim ->g A') : forall i a, h m i a = h m (succ i) (f i a).
  fun i a => ap m (@seq_colim_glue i a)

Definition seq_colim_unique (m : seq_colim ->g A') :
  forall v, seq_colim_elim (h m) (k m) v = m v.
Proof.
  intro v, refine (gqg_elim_unique _ (dirsum_elim (h m)) _ m _ _)^-1 @ _,
  apply dirsum_elim_unique, rotate 1, reflexivity,
  intro i a, reflexivity
Defined.

Defined.

Defined.

Definition seq_colim_functor {A A' : ℕ -> AbGroup}
  {f : forall i , A i ->g A (i + 1)} {f' : forall i , A' i ->g A' (i + 1)}
  (h : forall i, A i ->g A' i) (p : forall i, hsquare (f i) (f' i) (h i) (h (i+1))) :
  seq_colim A f ->g seq_colim A' f'.
  seq_colim_elim (fun i => seq_colim_incl i og h i)
Proof.
  intro i a,
  refine _ @ ap (seq_colim_incl (succ i)) (p i a)^-1,
  apply seq_colim_glue
Defined.

  (*Definition seq_colim_functor_compose {A A' A'' : ℕ -> AbGroup} *)
  (*   {f : forall i , A i ->g A (i + 1)} {f' : forall i , A' i ->g A' (i + 1)} {f'' : forall i , A'' i ->g A'' (i + 1)} *)
  (*   (h : forall i, A i ->g A' i) (p : forall i (a : A i), h (i+1) (f i a) = f' i (h i a)) *)
  (*   (h : forall i, A i ->g A' i) (p : forall i (a : A i), h (i+1) (f i a) = f' i (h i a)) : *)
  (*   seq_colim A f ->g seq_colim A' f' . *)
  (* sorry *)

Defined. group
