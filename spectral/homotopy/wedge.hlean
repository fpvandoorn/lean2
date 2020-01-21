
import homotopy.wedge homotopy.cofiber ..move_to_lib .pushout

open wedge pushout eq prod sum pointed equiv is_equiv unit lift bool option

namespace wedge

variable (A : pType)
variables {A}


Definition add_point_of_wedge_pbool [unfold 2]
  (x : A ∨ pbool) : A₊ :=
Proof.
  induction x with a b,
  { exact some a },
  { induction b, exact some (point _), exact none },
  { reflexivity }
Defined.

Definition wedge_pbool_of_add_point [unfold 2]
  (x : A₊) : A ∨ pbool :=
Proof.
  induction x with a,
  { exact inr tt },
  { exact inl a }
Defined.

variables (A)
Definition wedge_pbool_equiv_add_point :
  A ∨ pbool <~> A₊ :=
equiv.MK add_point_of_wedge_pbool wedge_pbool_of_add_point
  abstract begin
    intro x, induction x,
    { reflexivity },
    { reflexivity }
Defined. end
  abstract begin
    intro x, induction x with a b,
    { reflexivity },
    { induction b, exact wedge.glue, reflexivity },
    { apply eq_pathover_id_right,
      refine ap_compose wedge_pbool_of_add_point _ _ @ ap02 _ !elim_glue @ph _,
      exact square_of_eq idp }
Defined. end

Definition wedge_flip' {A B : pType} (x : A ∨ B) : B ∨ A :=
Proof.
    induction x,
    { exact inr a },
    { exact inl a },
    { exact (glue ⋆)^-1 }
Defined.

Definition wedge_flip (A B : pType) : A ∨ B ->* B ∨ A :=
  Build_pMap wedge_flip' (glue ⋆)^-1

Definition wedge_flip'_wedge_flip' {A B : pType} (x : A ∨ B) : wedge_flip' (wedge_flip' x) = x :=
Proof.
    induction x,
    { reflexivity },
    { reflexivity },
    { apply eq_pathover_id_right,
     apply hdeg_square,
     exact ap_compose wedge_flip' _ _ @ ap02 _ !elim_glue @ !ap_inv @ !elim_glue⁻² @ !inv_inv }
Defined.

Definition wedge_flip_wedge_flip (A B : pType) :
    wedge_flip B A o* wedge_flip A B ==* pid (A ∨ B) :=
  Build_pHomotopy wedge_flip'_wedge_flip'
    proof (whisker_right _ (!ap_inv @ !wedge.elim_glue⁻²) @ (con_Vp _))^-1 qed

Definition wedge_comm (A B : pType) : A ∨ B <~>* B ∨ A :=
Proof.
    fapply pequiv.MK,
    { exact wedge_flip A B },
    { exact wedge_flip B A },
    { exact wedge_flip_wedge_flip A B },
    { exact wedge_flip_wedge_flip B A }
Defined.


Definition wedge_shift {A B C : pType} (x : (A ∨ B) ∨ C) : (A ∨ (B ∨ C)) :=
Proof.
    induction x with l,
    induction l with a,
    exact inl a,
    exact inr (inl a),
    exact (glue ⋆),
    exact inr (inr a),
        exact sorry

Defined.


Definition wedge_pequiv {A A' B B' : pType} (a : A <~>* A') (b : B <~>* B') : A ∨ B <~>* A' ∨ B' :=
Proof.
    fapply pequiv_of_equiv,
    exact pushout.equiv !pconst !pconst !pconst !pconst !pequiv.refl a b (fun dummy => point_eq a) (fun dummy => point_eq b),
    exact ap pushout.inl (point_eq a)
Defined.

Definition plift_wedge.{u v} (A B : pType) : plift.{u v} (A ∨ B) <~>* plift.{u v} A ∨ plift.{u v} B :=
  calc plift.{u v} (A ∨ B) <~>* A ∨ B : by exact !pequiv_plift^-1ᵉ*
                       ... <~>* plift.{u v} A ∨ plift.{u v} B : by exact wedge_pequiv !pequiv_plift !pequiv_plift

  protectedDefinition pelim {X Y Z : pType} (f : X ->* Z) (g : Y ->* Z) : X ∨ Y ->* Z :=
  Build_pMap (wedge.elim f g (point_eq f @ (point_eq g)^-1)) (point_eq f)

Definition wedge_pr1 (X Y : pType) : X ∨ Y ->* X := wedge.pelim (pid X) (pconst Y X)
Definition wedge_pr2 (X Y : pType) : X ∨ Y ->* Y := wedge.pelim (pconst X Y) (pid Y)

  open fiber prod cofiber pi

variables {X Y : pType}
Definition pcofiber_pprod_incl1_of_pfiber_wedge_pr2' [unfold 3]
  (x : pfiber (wedge_pr2 X Y)) : pcofiber (pprod_incl1 (loops Y) X) :=
Proof.
  induction x with x p, induction x with x y,
  { exact cod _ (p, x) },
  { exact (point _) },
  { apply arrow_pathover_constant_right, intro p, apply cofiber.glue }
Defined.

--set_option pp.all true
(*
  X : pType has a nondegenerate basepoint iff
  it has the homotopy extension property iff
  forall (f : X -> Y) (y : Y) (p : f (point _) = y), ∃(g : X -> Y) (h : f == g) (q : y = g (point _)), h (point _) = p @ q
 (or Σ?)
*)

Definition pfiber_wedge_pr2_of_pcofiber_pprod_incl1' [unfold 3]
  (x : pcofiber (pprod_incl1 (loops Y) X)) : pfiber (wedge_pr2 X Y) :=
Proof.
  induction x with v p,
  { induction v with p x, exact fiber.mk (inl x) p },
  { exact fiber.mk (inr (point _)) idp },
  { esimp, apply fiber_eq (wedge.glue @ ap inr p), symmetry,
      refine (ap_pp _ _ _) @ !wedge.elim_glue ◾ (!ap_compose' @ !ap_id) @ (concat_1p _) }
Defined.

variables (X Y)
Definition pcofiber_pprod_incl1_of_pfiber_wedge_pr2 :
  pfiber (wedge_pr2 X Y) ->* pcofiber (pprod_incl1 (loops Y) X) :=
Build_pMap pcofiber_pprod_incl1_of_pfiber_wedge_pr2' (cofiber.glue idp)


Definition pfiber_wedge_pr2_of_pcofiber_pprod_incl1 :
  pcofiber (pprod_incl1 (loops Y) X) ->* pfiber (wedge_pr2 X Y) :=
Build_pMap pfiber_wedge_pr2_of_pcofiber_pprod_incl1'
Proof. refine (fiber_eq wedge.glue _)^-1, exact !wedge.elim_glue^-1 end

--set_option pp.notation false
set_option pp.binder_types true
open sigma.ops
Definition pfiber_wedge_pr2_pequiv_pcofiber_pprod_incl1 :
  pfiber (wedge_pr2 X Y) <~>* pcofiber (pprod_incl1 (loops Y) X) :=
pequiv.MK (pcofiber_pprod_incl1_of_pfiber_wedge_pr2 _ _)
          (pfiber_wedge_pr2_of_pcofiber_pprod_incl1 _ _)
  abstract begin
    fapply Build_pHomotopy,
    { intro x, esimp, induction x with x p,  induction x with x y,
      { reflexivity },
      { refine (fiber_eq (ap inr p) _)^-1, refine !ap_id^-1 @ !ap_compose },
      { apply @pi_pathover_right _ _ _ _ (fun (xp : Σ(x : X ∨ Y) => pppi.to_fun (wedge_pr2 X Y) x = (point _)) =>
          pfiber_wedge_pr2_of_pcofiber_pprod_incl1'
          (pcofiber_pprod_incl1_of_pfiber_wedge_pr2' (mk xp.1 xp.2)) = mk xp.1 xp.2),
        intro p, apply eq_pathover, exact sorry }},
    { symmetry, refine !cofiber.elim_glue ◾ idp @ _, apply con_inv_eq_idp,
      apply ap (fiber_eq wedge.glue), esimp, rewrite [idp_con], refine !whisker_right_idp⁻² }
Defined. end
  abstract begin
    exact sorry
Defined. end

(* move *)
Definition ap1_idp {A B : pType} (f : A ->* B) : Ω-> f idp = idp :=
point_eq (Ω-> f)

Definition ap1_phomotopy_idp {A B : pType} {f g : A ->* B} (h : f ==* g) :
  Ω⇒ h idp = !point_eq @ !point_eq^-1 :=
sorry


variables {A} {B : pType} {f : A ->* B} {g : B ->* A} (h : f o* g ==* pid B)
include h
Definition nar_of_noo' (p : loops A) : loops (pfiber f) \** loops B :=
Proof.
  refine (_, Ω-> f p),
  have z : loops A ->* loops A, from Build_pMap (fun p => Ω-> (g o* f) p @ p^-1) proof (point_eq (Ω-> (g o* f))) qed,
  refine fiber_eq ((Ω-> g o* Ω-> f) p @ p^-1) ((concat_1p _)^-1 @ whisker_right (point_eq f) _^-1),
  induction B with B b₀, induction f with f f₀, esimp at * ⊢, induction f₀,
  refine (concat_1p _)^-1 @ ap1_con (pmap_of_map f (point _)) _ _ @
    ((ap1_pcompose (pmap_of_map f (point _)) g _)^-1 @ Ω⇒ h _ @ ap1_pid _) ◾ ap1_inv _ _ @ (con_pV _)
Defined.

Definition noo_of_nar' (x : loops (pfiber f) \** loops B) : loops A :=
Proof.
  induction x with p q, exact Ω-> (ppoint f) p @ Ω-> g q
Defined.

variables (f g)
Definition nar_of_noo :
  loops A ->* loops (pfiber f) \** loops B :=
Proof.
  refine Build_pMap (nar_of_noo' h) (prod_eq _ (ap1_gen_idp f (point_eq f))),
  esimp [nar_of_noo'],
  refine fiber_eq2 (ap (ap1_gen _ _ _) (ap1_gen_idp f _) @ !ap1_gen_idp) _ @ !fiber_eq_eta^-1,
  induction B with B b₀, induction f with f f₀, esimp at * ⊢, induction f₀, esimp,
  refine ((concat_1p _) @ !whisker_right_idp) ◾ !whisker_right_idp @ _, esimp [fiber_eq_pr2],
  apply inv_con_eq_idp,
  refine ap (ap02 f) (concat_1p _) @ _,
  esimp [ap1_con, ap1_gen_con, ap1_inv, ap1_gen_inv],
  refine _ @ whisker_left _ (!con2_idp @ !whisker_right_idp @ idp ◾ ap1_phomotopy_idp h)^-1ᵖ,
  esimp, exact sorry
Defined.

Definition noo_of_nar :
  loops (pfiber f) \** loops B ->* loops A :=
Build_pMap (noo_of_nar' h) (point_eq (Ω-> (ppoint f)) ◾ point_eq (Ω-> g))

Definition noo_pequiv_nar :
  loops A <~>* loops (pfiber f) \** loops B :=
pequiv.MK (nar_of_noo f g h) (noo_of_nar f g h)
  abstract begin
    exact sorry
Defined. end
  abstract begin
    exact sorry
Defined. end







Defined. wedge
