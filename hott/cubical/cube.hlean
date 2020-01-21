(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn, Jakob von Raumer

Cubes
*)

import .square

open equiv is_equiv sigma sigma.ops

namespace eq

  inductive cube {A : Type} {a₀₀₀ : A} : forall {a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₂₀₂ a₀₂₂ a₂₂₂ : A}
  {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂}
  {p₁₂₀ : a₀₂₀ = a₂₂₀} {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₂₀₁ : a₂₀₀ = a₂₀₂}
  {p₁₀₂ : a₀₀₂ = a₂₀₂} {p₀₁₂ : a₀₀₂ = a₀₂₂} {p₀₂₁ : a₀₂₀ = a₀₂₂}
  {p₁₂₂ : a₀₂₂ = a₂₂₂} {p₂₁₂ : a₂₀₂ = a₂₂₂} {p₂₂₁ : a₂₂₀ = a₂₂₂}
  (s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁)
  (s₂₁₁ : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁)
  (s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁)
  (s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁)
  (s₁₁₀ : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀)
  (s₁₁₂ : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂), Type.
  idc : cube ids ids ids ids ids ids

  variables {A B : Type} {a₀₀₀ a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₂₀₂ a₀₂₂ a₂₂₂ a a' : A}
  {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂}
  {p₁₂₀ : a₀₂₀ = a₂₂₀} {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₂₀₁ : a₂₀₀ = a₂₀₂}
  {p₁₀₂ : a₀₀₂ = a₂₀₂} {p₀₁₂ : a₀₀₂ = a₀₂₂} {p₀₂₁ : a₀₂₀ = a₀₂₂}
  {p₁₂₂ : a₀₂₂ = a₂₂₂} {p₂₁₂ : a₂₀₂ = a₂₂₂} {p₂₂₁ : a₂₂₀ = a₂₂₂}
  {s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁}
  {s₂₁₁ : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}
  {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁}
  {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}
  {s₁₁₀ : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀}
  {s₁₁₂ : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
  {b₁ b₂ b₃ b₄ : B}
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂)

Definition idc            . @cube.idc
Definition idcube (a : A) . @cube.idc A a

  variables (s₁₁₀ s₁₀₁)
Definition refl1 : cube s₀₁₁ s₀₁₁ hrfl hrfl vrfl vrfl.
  by induction s₀₁₁; exact idc

Definition refl2 : cube hrfl hrfl s₁₀₁ s₁₀₁ hrfl hrfl.
  by induction s₁₀₁; exact idc

Definition refl3 : cube vrfl vrfl vrfl vrfl s₁₁₀ s₁₁₀.
  by induction s₁₁₀; exact idc

  variables {s₁₁₀ s₁₀₁}
Definition rfl1 : cube s₀₁₁ s₀₁₁ hrfl hrfl vrfl vrfl . !refl1

Definition rfl2 : cube hrfl hrfl s₁₀₁ s₁₀₁ hrfl hrfl . !refl2

Definition rfl3 : cube vrfl vrfl vrfl vrfl s₁₁₀ s₁₁₀ . !refl3

  (* Variables for composition *)
  variables {a₄₀₀ a₄₀₂ a₄₂₀ a₄₂₂ a₀₄₀ a₀₄₂ a₂₄₀ a₂₄₂ a₀₀₄ a₀₂₄ a₂₀₄ a₂₂₄ : A}
  {p₃₀₀ : a₂₀₀ = a₄₀₀} {p₃₀₂ : a₂₀₂ = a₄₀₂} {p₃₂₀ : a₂₂₀ = a₄₂₀} {p₃₂₂ : a₂₂₂ = a₄₂₂}
  {p₄₀₁ : a₄₀₀ = a₄₀₂} {p₄₁₀ : a₄₀₀ = a₄₂₀} {p₄₁₂ : a₄₀₂ = a₄₂₂} {p₄₂₁ : a₄₂₀ = a₄₂₂}
  {p₀₃₀ : a₀₂₀ = a₀₄₀} {p₀₃₂ : a₀₂₂ = a₀₄₂} {p₂₃₀ : a₂₂₀ = a₂₄₀} {p₂₃₂ : a₂₂₂ = a₂₄₂}
  {p₀₄₁ : a₀₄₀ = a₀₄₂} {p₁₄₀ : a₀₄₀ = a₂₄₀} {p₁₄₂ : a₀₄₂ = a₂₄₂} {p₂₄₁ : a₂₄₀ = a₂₄₂}
  {p₀₀₃ : a₀₀₂ = a₀₀₄} {p₀₂₃ : a₀₂₂ = a₀₂₄} {p₂₀₃ : a₂₀₂ = a₂₀₄} {p₂₂₃ : a₂₂₂ = a₂₂₄}
  {p₀₁₄ : a₀₀₄ = a₀₂₄} {p₁₀₄ : a₀₀₄ = a₂₀₄} {p₁₂₄ : a₀₂₄ = a₂₂₄} {p₂₁₄ : a₂₀₄ = a₂₂₄}
  {s₃₀₁ : square p₃₀₀ p₃₀₂ p₂₀₁ p₄₀₁} {s₃₁₀ : square p₂₁₀ p₄₁₀ p₃₀₀ p₃₂₀}
  {s₃₁₂ : square p₂₁₂ p₄₁₂ p₃₀₂ p₃₂₂} {s₃₂₁ : square p₃₂₀ p₃₂₂ p₂₂₁ p₄₂₁}
  {s₄₁₁ : square p₄₁₀ p₄₁₂ p₄₀₁ p₄₂₁}
  {s₀₃₁ : square p₀₃₀ p₀₃₂ p₀₂₁ p₀₄₁} {s₁₃₀ : square p₀₃₀ p₂₃₀ p₁₂₀ p₁₄₀}
  {s₁₃₂ : square p₀₃₂ p₂₃₂ p₁₂₂ p₁₄₂} {s₂₃₁ : square p₂₃₀ p₂₃₂ p₂₂₁ p₂₄₁}
  {s₁₄₁ : square p₁₄₀ p₁₄₂ p₀₄₁ p₂₄₁}
  {s₀₁₃ : square p₀₁₂ p₀₁₄ p₀₀₃ p₀₂₃} {s₁₀₃ : square p₁₀₂ p₁₀₄ p₀₀₃ p₂₀₃}
  {s₁₂₃ : square p₁₂₂ p₁₂₄ p₀₂₃ p₂₂₃} {s₂₁₃ : square p₂₁₂ p₂₁₄ p₂₀₃ p₂₂₃}
  {s₁₁₄ : square p₀₁₄ p₂₁₄ p₁₀₄ p₁₂₄}
  (d : cube s₂₁₁ s₄₁₁ s₃₀₁ s₃₂₁ s₃₁₀ s₃₁₂)
  (e : cube s₀₃₁ s₂₃₁ s₁₂₁ s₁₄₁ s₁₃₀ s₁₃₂)
  (f : cube s₀₁₃ s₂₁₃ s₁₀₃ s₁₂₃ s₁₁₂ s₁₁₄)

  (* Composition of Cubes *)

  include c d
Definition cube_concat1 : cube s₀₁₁ s₄₁₁ (s₁₀₁ @h s₃₀₁) (s₁₂₁ @h s₃₂₁) (s₁₁₀ @v s₃₁₀) (s₁₁₂ @v s₃₁₂).
  by induction d; exact c
  omit d

  include e
Definition cube_concat2 : cube (s₀₁₁ @h s₀₃₁) (s₂₁₁ @h s₂₃₁) s₁₀₁ s₁₄₁ (s₁₁₀ @h s₁₃₀) (s₁₁₂ @h s₁₃₂).
  by induction e; exact c
  omit e

  include f
Definition cube_concat3 : cube (s₀₁₁ @v s₀₁₃) (s₂₁₁ @v s₂₁₃) (s₁₀₁ @v s₁₀₃) (s₁₂₁ @v s₁₂₃) s₁₁₀ s₁₁₄.
  by induction f; exact c
  omit f c

Definition eq_of_cube (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  transpose s₁₀₁^-1ᵛ @h s₁₁₀ @h transpose s₁₂₁ =
  whisker_square (eq_bot_of_square s₀₁₁) (eq_bot_of_square s₂₁₁) idp idp s₁₁₂.
  by induction c; reflexivity

Definition eq_of_deg12_cube {s s' : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀}
  (c : cube vrfl vrfl vrfl vrfl s s') : s = s'.
  by induction s; exact eq_of_cube c

Definition square_pathover {A B : Type} {a a' : A} {b₁ b₂ b₃ b₄ : A -> B}
  {f₁ : b₁ == b₂} {f₂ : b₃ == b₄} {f₃ : b₁ == b₃} {f₄ : b₂ == b₄} {p : a = a'}
  {q : square (f₁ a) (f₂ a) (f₃ a) (f₄ a)}
  {r : square (f₁ a') (f₂ a') (f₃ a') (f₄ a')}
  (s : cube (natural_square f₁ p) (natural_square f₂ p)
  (natural_square f₃ p) (natural_square f₄ p) q r) : q =[p] r.
  by induction p; apply pathover_idp_of_eq; exact eq_of_deg12_cube s

  (* a special case where the endpoints do not depend on `p` *)
Definition square_pathover'
  {f₁ : A -> b₁ = b₂} {f₂ : A -> b₃ = b₄} {f₃ : A -> b₁ = b₃} {f₄ : A -> b₂ = b₄}
  {p : a = a'}
  {q : square (f₁ a) (f₂ a) (f₃ a) (f₄ a)}
  {r : square (f₁ a') (f₂ a') (f₃ a') (f₄ a')}
  (s : cube (vdeg_square (ap f₁ p)) (vdeg_square (ap f₂ p))
  (vdeg_square (ap f₃ p)) (vdeg_square (ap f₄ p)) q r) : q =[p] r.
  by induction p;apply pathover_idp_of_eq;exact eq_of_deg12_cube s

  (* Transporting along a square *)

  (* TODO: remove: they are defined again below *)
Definition cube_transport110 {s₁₁₀' : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀}
  (p : s₁₁₀ = s₁₁₀') (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀' s₁₁₂.
  by induction p; exact c

Definition cube_transport112 {s₁₁₂' : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
  (p : s₁₁₂ = s₁₁₂') (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂'.
  by induction p; exact c

Definition cube_transport011 {s₀₁₁' : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁}
  (p : s₀₁₁ = s₀₁₁') (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  cube s₀₁₁' s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂.
  by induction p; exact c

Definition cube_transport211 {s₂₁₁' : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}
  (p : s₂₁₁ = s₂₁₁') (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  cube s₀₁₁ s₂₁₁' s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂.
  by induction p; exact c

Definition cube_transport101 {s₁₀₁' : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁}
  (p : s₁₀₁ = s₁₀₁') (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  cube s₀₁₁ s₂₁₁ s₁₀₁' s₁₂₁ s₁₁₀ s₁₁₂.
  by induction p; exact c

Definition cube_transport121 {s₁₂₁' : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}
  (p : s₁₂₁ = s₁₂₁') (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁' s₁₁₀ s₁₁₂.
  by induction p; exact c

  (* Each equality between squares leads to a cube which is degenerate in one
  dimension. *)

Definition deg1_cube {s₁₁₀' : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀} (p : s₁₁₀ = s₁₁₀') :
  cube s₁₁₀ s₁₁₀' hrfl hrfl vrfl vrfl.
  by induction p; exact rfl1

Definition deg2_cube {s₁₁₀' : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀} (p : s₁₁₀ = s₁₁₀') :
  cube hrfl hrfl s₁₁₀ s₁₁₀' hrfl hrfl.
  by induction p; exact rfl2

Definition deg3_cube {s₁₁₀' : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀} (p : s₁₁₀ = s₁₁₀') :
  cube vrfl vrfl vrfl vrfl s₁₁₀ s₁₁₀'.
  by induction p; exact rfl3

  (* For each square of parralel equations, there are cubes where the square's
  sides appear in a degenerated way and two opposite sides are ids's *)

  section
  variables {a₀ a₁ : A} {p₀₀ p₀₂ p₂₀ p₂₂ : a₀ = a₁} {s₁₀ : p₀₀ = p₂₀}
  {s₁₂ : p₀₂ = p₂₂} {s₀₁ : p₀₀ = p₀₂} {s₂₁ : p₂₀ = p₂₂}
  (sq : square s₁₀ s₁₂ s₀₁ s₂₁)

  include sq

Definition ids3_cube_of_square : cube (hdeg_square s₀₁)
  (hdeg_square s₂₁) (hdeg_square s₁₀) (hdeg_square s₁₂) ids ids.
  by induction p₀₀; induction sq; apply idc

Definition ids1_cube_of_square : cube ids ids
  (vdeg_square s₁₀) (vdeg_square s₁₂) (hdeg_square s₀₁) (hdeg_square s₂₁).
  by induction p₀₀; induction sq; apply idc

Definition ids2_cube_of_square : cube (vdeg_square s₁₀) (vdeg_square s₁₂)
  ids ids (vdeg_square s₀₁) (vdeg_square s₂₁).
  by induction p₀₀; induction sq; apply idc

Defined.

  (* Cube fillers *)

  section cube_fillers
  variables (s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁)

Definition cube_fill110 : Σ lid, cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ lid s₁₁₂.
Proof.
  induction s₀₁₁, induction s₂₁₁,
  let fillsq . square_fill_l (eq_of_vdeg_square s₁₀₁)
  (eq_of_hdeg_square s₁₁₂) (eq_of_vdeg_square s₁₂₁),
  apply sigma.mk,
  apply cube_transport101 (left_inv (vdeg_square_equiv _ _) s₁₀₁),
  apply cube_transport112 (left_inv (hdeg_square_equiv _ _) s₁₁₂),
  apply cube_transport121 (left_inv (vdeg_square_equiv _ _) s₁₂₁),
  apply ids1_cube_of_square, exact fillsq.2
Defined.

Definition cube_fill112 : Σ lid, cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ lid.
Proof.
  induction s₀₁₁, induction s₂₁₁,
  let fillsq . square_fill_r (eq_of_vdeg_square s₁₀₁)
  (eq_of_hdeg_square s₁₁₀) (eq_of_vdeg_square s₁₂₁),
  apply sigma.mk,
  apply cube_transport101 (left_inv (vdeg_square_equiv _ _) s₁₀₁),
  apply cube_transport110 (left_inv (hdeg_square_equiv _ _) s₁₁₀),
  apply cube_transport121 (left_inv (vdeg_square_equiv _ _) s₁₂₁),
  apply ids1_cube_of_square, exact fillsq.2,
Defined.

Definition cube_fill011 : Σ lid, cube lid s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂.
Proof.
  induction s₁₀₁, induction s₁₂₁,
  let fillsq . square_fill_t (eq_of_vdeg_square s₁₁₀) (eq_of_vdeg_square s₁₁₂)
  (eq_of_vdeg_square s₂₁₁),
  apply sigma.mk,
  apply cube_transport110 (left_inv (vdeg_square_equiv _ _) s₁₁₀),
  apply cube_transport211 (left_inv (vdeg_square_equiv _ _) s₂₁₁),
  apply cube_transport112 (left_inv (vdeg_square_equiv _ _) s₁₁₂),
  apply ids2_cube_of_square, exact fillsq.2,
Defined.

Definition cube_fill211 : Σ lid, cube s₀₁₁ lid s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂.
Proof.
  induction s₁₀₁, induction s₁₂₁,
  let fillsq . square_fill_b (eq_of_vdeg_square s₀₁₁) (eq_of_vdeg_square s₁₁₀)
  (eq_of_vdeg_square s₁₁₂),
  apply sigma.mk,
  apply cube_transport011 (left_inv (vdeg_square_equiv _ _) s₀₁₁),
  apply cube_transport110 (left_inv (vdeg_square_equiv _ _) s₁₁₀),
  apply cube_transport112 (left_inv (vdeg_square_equiv _ _) s₁₁₂),
  apply ids2_cube_of_square, exact fillsq.2,
Defined.

Definition cube_fill101 : Σ lid, cube s₀₁₁ s₂₁₁ lid s₁₂₁ s₁₁₀ s₁₁₂.
Proof.
  induction s₁₁₀, induction s₁₁₂,
  let fillsq . square_fill_t (eq_of_hdeg_square s₀₁₁) (eq_of_hdeg_square s₂₁₁)
  (eq_of_hdeg_square s₁₂₁),
  apply sigma.mk,
  apply cube_transport011 (left_inv (hdeg_square_equiv _ _) s₀₁₁),
  apply cube_transport211 (left_inv (hdeg_square_equiv _ _) s₂₁₁),
  apply cube_transport121 (left_inv (hdeg_square_equiv _ _) s₁₂₁),
  apply ids3_cube_of_square, exact fillsq.2,
Defined.

Definition cube_fill121 : Σ lid, cube s₀₁₁ s₂₁₁ s₁₀₁ lid s₁₁₀ s₁₁₂.
Proof.
  induction s₁₁₀, induction s₁₁₂,
  let fillsq . square_fill_b (eq_of_hdeg_square s₁₀₁) (eq_of_hdeg_square s₀₁₁)
  (eq_of_hdeg_square s₂₁₁),
  apply sigma.mk,
  apply cube_transport101 (left_inv (hdeg_square_equiv _ _) s₁₀₁),
  apply cube_transport011 (left_inv (hdeg_square_equiv _ _) s₀₁₁),
  apply cube_transport211 (left_inv (hdeg_square_equiv _ _) s₂₁₁),
  apply ids3_cube_of_square, exact fillsq.2,
Defined.

Defined. cube_fillers

  (* Apply a non-dependent function to an entire cube *)

  include c
Definition apc (f : A -> B) :
  cube (aps f s₀₁₁) (aps f s₂₁₁) (aps f s₁₀₁) (aps f s₁₂₁) (aps f s₁₁₀) (aps f s₁₁₂).
  by cases c; exact idc
  omit c

  (* Transpose a cube (swap dimensions) *)

  include c
Definition transpose12 : cube s₁₀₁ s₁₂₁ s₀₁₁ s₂₁₁ (transpose s₁₁₀) (transpose s₁₁₂).
  by cases c; exact idc

Definition transpose13 : cube s₁₁₀ s₁₁₂ (transpose s₁₀₁) (transpose s₁₂₁) s₀₁₁ s₂₁₁.
  by cases c; exact idc

Definition transpose23 : cube (transpose s₀₁₁) (transpose s₂₁₁) (transpose s₁₁₀)
  (transpose s₁₁₂) (transpose s₁₀₁) (transpose s₁₂₁).
  by cases c; exact idc
  omit c

  (* Inverting a cube along one dimension *)

  include c
Definition cube_inverse1 : cube s₂₁₁ s₀₁₁ s₁₀₁^-1ʰ s₁₂₁^-1ʰ s₁₁₀^-1ᵛ s₁₁₂^-1ᵛ.
  by cases c; exact idc

Definition cube_inverse2 : cube s₀₁₁^-1ʰ s₂₁₁^-1ʰ s₁₂₁ s₁₀₁ s₁₁₀^-1ʰ s₁₁₂^-1ʰ.
  by cases c; exact idc

Definition cube_inverse3 : cube s₀₁₁^-1ᵛ s₂₁₁^-1ᵛ s₁₀₁^-1ᵛ s₁₂₁^-1ᵛ s₁₁₂ s₁₁₀.
  by cases c; exact idc
  omit c

Definition eq_concat1 {s₀₁₁' : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁} (r : s₀₁₁' = s₀₁₁)
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) : cube s₀₁₁' s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂.
  by induction r; exact c

Definition concat1_eq {s₂₁₁' : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) (r : s₂₁₁ = s₂₁₁')
  : cube s₀₁₁ s₂₁₁' s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂.
  by induction r; exact c

Definition eq_concat2 {s₁₀₁' : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁} (r : s₁₀₁' = s₁₀₁)
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) : cube s₀₁₁ s₂₁₁ s₁₀₁' s₁₂₁ s₁₁₀ s₁₁₂.
  by induction r; exact c

Definition concat2_eq {s₁₂₁' : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) (r : s₁₂₁ = s₁₂₁')
  : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁' s₁₁₀ s₁₁₂.
  by induction r; exact c

Definition eq_concat3 {s₁₁₀' : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀} (r : s₁₁₀' = s₁₁₀)
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀' s₁₁₂.
  by induction r; exact c

Definition concat3_eq {s₁₁₂' : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) (r : s₁₁₂ = s₁₁₂')
  : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂'.
  by induction r; exact c

  infix ` @1 `:75 . cube_concat1
  infix ` @2 `:75 . cube_concat2
  infix ` @3 `:75 . cube_concat3
  infixr ` @p1 `:75 . eq_concat1
  infixl ` @1p `:75 . concat1_eq
  infixr ` @p2 `:75 . eq_concat2
  infixl ` @2p `:75 . concat2_eq
  infixr ` @p3 `:75 . eq_concat3
  infixl ` @3p `:75 . concat3_eq

Definition whisker001 {p₀₀₁' : a₀₀₀ = a₀₀₂} (q : p₀₀₁' = p₀₀₁)
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) : cube (q @ph s₀₁₁) s₂₁₁ (q @ph s₁₀₁) s₁₂₁ s₁₁₀ s₁₁₂.
  by induction q; exact c

Definition whisker021 {p₀₂₁' : a₀₂₀ = a₀₂₂} (q : p₀₂₁' = p₀₂₁)
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  cube (s₀₁₁ @hp q^-1) s₂₁₁ s₁₀₁ (q @ph s₁₂₁) s₁₁₀ s₁₁₂.
  by induction q; exact c

Definition whisker021' {p₀₂₁' : a₀₂₀ = a₀₂₂} (q : p₀₂₁ = p₀₂₁')
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  cube (s₀₁₁ @hp q) s₂₁₁ s₁₀₁ (q^-1 @ph s₁₂₁) s₁₁₀ s₁₁₂.
  by induction q; exact c

Definition whisker201 {p₂₀₁' : a₂₀₀ = a₂₀₂} (q : p₂₀₁' = p₂₀₁)
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  cube s₀₁₁ (q @ph s₂₁₁) (s₁₀₁ @hp q^-1) s₁₂₁ s₁₁₀ s₁₁₂.
  by induction q; exact c

Definition whisker201' {p₂₀₁' : a₂₀₀ = a₂₀₂} (q : p₂₀₁ = p₂₀₁')
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  cube s₀₁₁ (q^-1 @ph s₂₁₁) (s₁₀₁ @hp q) s₁₂₁ s₁₁₀ s₁₁₂.
  by induction q; exact c

Definition whisker221 {p₂₂₁' : a₂₂₀ = a₂₂₂} (q : p₂₂₁ = p₂₂₁')
  (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) : cube s₀₁₁ (s₂₁₁ @hp q) s₁₀₁ (s₁₂₁ @hp q) s₁₁₀ s₁₁₂.
  by induction q; exact c

Definition move221 {p₂₂₁' : a₂₂₀ = a₂₂₂} {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁'} (q : p₂₂₁ = p₂₂₁')
  (c : cube s₀₁₁ (s₂₁₁ @hp q) s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  cube s₀₁₁ s₂₁₁ s₁₀₁ (s₁₂₁ @hp q^-1) s₁₁₀ s₁₁₂.
  by induction q; exact c

Definition move201 {p₂₀₁' : a₂₀₀ = a₂₀₂} {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁'}  (q : p₂₀₁' = p₂₀₁)
  (c : cube s₀₁₁ (q @ph s₂₁₁) s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
  cube s₀₁₁ s₂₁₁ (s₁₀₁ @hp q) s₁₂₁ s₁₁₀ s₁₁₂.
  by induction q; exact c

Defined. eq
