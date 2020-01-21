(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
*)

import .seq_colim types.unit

open eq nat is_equiv equiv is_trunc pi unit function prod unit sigma sigma.ops sum prod trunc fin
  algebra

namespace seq_colim

  universe variable u
  variables {A : ℕ -> Type.{u}} (f : seq_diagram A)
  variables {n : ℕ} (a : A n)

Definition arrow_colim_of_colim_arrow {X : Type}
  (g : seq_colim (seq_diagram_arrow_left f X)) (x : X) : seq_colim f.
Proof. induction g with n g n g, exact ι f (g x), exact glue f (g x) end

Definition omega_compact [class] (X : Type) : Type.
  forall (A : ℕ -> Type) (f : seq_diagram A),
  is_equiv (arrow_colim_of_colim_arrow f :
  seq_colim (seq_diagram_arrow_left f X) -> (X -> seq_colim f))

Definition equiv_of_omega_compact (X : Type) [H : omega_compact X]
  {A : ℕ -> Type} (f : seq_diagram A) :
  seq_colim (seq_diagram_arrow_left f X) <~> (X -> seq_colim f).
  equiv.mk _ (H f)

Definition omega_compact_of_equiv (X : Type)
  (H : forall (A : ℕ -> Type) (f : seq_diagram A),
  seq_colim (seq_diagram_arrow_left f X) <~> (X -> seq_colim f))
  (p : forall (A : ℕ -> Type) (f : seq_diagram A) {n : ℕ} (g : X -> A n) (x : X),
  H f (ι _ g) x = ι _ (g x))
  (q : forall (A : ℕ -> Type) (f : seq_diagram A) {n : ℕ} (g : X -> A n) (x : X),
  square (p f (@f n o g) x) (p f g x) (ap (fun g => H f g x)
  (glue (seq_diagram_arrow_left f X) g)) (glue f (g x)))
  : omega_compact X.
  fun A f => is_equiv_of_equiv_of_homotopy (H f)
Proof.
  intro g, apply eq_of_homotopy, intro x,
  induction g with n g n g,
  { exact p f g x },
  { apply eq_pathover, refine _ @hp !elim_glue^-1, exact q f g x }
Defined.

  local attribute is_contr_seq_colim [instance]
Definition is_contr_empty_arrow [instance] (X : Type) : is_contr (empty -> X).
  by apply is_trunc_pi; contradiction

Definition omega_compact_empty [instance] : omega_compact empty.
Proof.
  intro A f,
  fapply adjointify,
  { intro g, exact ι' _ 0 empty.elim},
  { intro g, apply eq_of_homotopy, contradiction},
  { intro h, apply is_prop.elim}
Defined.

Definition omega_compact_unit' [instance] : omega_compact unit.
Proof.
  intro A f,
  fapply adjointify,
  { intro g, induction g ⋆,
  { exact ι _ (fun x => a)},
  { apply glue}},
  { intro g, apply eq_of_homotopy, intro u, induction u,
  induction g ⋆,
  { reflexivity},
  { esimp, apply eq_pathover_id_right, apply hdeg_square,
  refine ap_compose (fun x => arrow_colim_of_colim_arrow f x ⋆) _ _ @ _,
  refine ap02 _ !elim_glue @ _, apply elim_glue}},
  { intro h, induction h with n h n h,
  { esimp, apply ap (ι' _ n), apply unit_arrow_eq},
  { esimp, apply eq_pathover_id_right,
  refine ap_compose (seq_colim.elim _ _ _) _ _ @ph _,
  refine ap02 _ !elim_glue @ph _,
  refine !elim_glue @ph _,
  refine _ @pv natural_square_tr (@glue _ (seq_diagram_arrow_left f unit) n) (unit_arrow_eq h),
  refine _ @ (ap_compose (ι' _ _) _ _)^-1,
  apply ap02, unfold [seq_diagram_arrow_left],
  apply unit_arrow_eq_compose}}
Defined.

Definition omega_compact_unit [instance] : omega_compact unit.
Proof.
  fapply omega_compact_of_equiv,
  { intro A f, refine _ @e !arrow_unit_left^-1ᵉ, fapply seq_colim_equiv,
  { intro n, apply arrow_unit_left },
  intro n f, reflexivity },
  { intros, induction x, reflexivity },
  { intros, induction x, esimp, apply hdeg_square, exact !elim_glue @ (concat_1p _) },
Defined.

  local attribute equiv_of_omega_compact
Definition omega_compact_prod [instance] {X Y : Type} [omega_compact.{_ u} X]
  [omega_compact.{u u} Y] : omega_compact.{_ u} (X \* Y).
Proof.
  fapply omega_compact_of_equiv,
  { intro A f,
  exact calc
  seq_colim (seq_diagram_arrow_left f (X \* Y))
  <~> seq_colim (seq_diagram_arrow_left (seq_diagram_arrow_left f Y) X) :
Proof.
  apply seq_colim_equiv (fun n => !imp_imp_equiv_prod_imp^-1ᵉ),
  intro n f, reflexivity
Defined.
  ... <~> (X -> seq_colim (seq_diagram_arrow_left f Y))  : !equiv_of_omega_compact
  ... <~> (X -> Y -> seq_colim f) : arrow_equiv_arrow_right _ !equiv_of_omega_compact
  ... <~> (X \* Y -> seq_colim f) : imp_imp_equiv_prod_imp },
  { intros, induction x with x y, reflexivity },
  { intros, induction x with x y, apply hdeg_square,
  refine ap_compose (fun z => arrow_colim_of_colim_arrow f z y) _ _ @ _,
  refine ap02 _ (ap_compose (fun z => arrow_colim_of_colim_arrow _ z x) _ _) @ _,
  refine ap02 _ (ap02 _ !elim_glue) @ _, refine ap02 _ (ap02 _ (concat_1p _)) @ _, esimp,
  refine ap02 _ !elim_glue @ _, apply elim_glue }
Defined.

Definition not_omega_compact_nat : ¬(omega_compact.{0 0} ℕ).
assume H,
let e . equiv_of_omega_compact ℕ seq_diagram_fin @e
  arrow_equiv_arrow_right _ seq_colim_fin_equiv in
Proof.
  have forall x, ∥ Σn, forall m, e x m < n ∥,
Proof.
  intro f, induction f using seq_colim.rec_prop with n f,
  refine tr ⟨n, _⟩, intro m, exact is_lt (f m)
Defined.,
  induction this (e^-1ᵉ id) with x, induction x with n H2,
  apply lt.irrefl n,
  refine lt_of_le_of_lt (le_of_eq _) (H2 n),
  exact ap10 (right_inv e id)^-1 n
Defined.

exit
  print seq_diagram_over
Definition seq_colim_over_equiv {X : Type} {A : X -> ℕ -> Type} (g : forall (x n), A x n -> A x (succ n))
  (x : X)
  : @seq_colim_over _ (constant_seq X) _ _ <~> seq_colim (@g x).
Proof.

Defined.

Definition seq_colim_pi_equiv {X : Type} {A : X -> ℕ -> Type} (g : forall (x n), A x n -> A x (succ n))
  [omega_compact X] : (forall x, seq_colim (@g x)) <~> seq_colim (seq_diagram_pi g).
Proof.
  refine !pi_equiv_arrow_sigma @e _,
  refine sigma_equiv_sigma_left (arrow_equiv_arrow_right X (sigma_equiv_sigma_left (seq_colim_constant_seq X)^-1ᵉ)) @e _,
  exact sigma_equiv_sigma_left (arrow_equiv_arrow_right X _) @e _,
Defined.

  set_option pp.universes true
  print seq_diagram_arrow_left

Defined. seq_colim
