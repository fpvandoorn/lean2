(*
In this file we give a consequence of the Yoneda lemma for pointed types which we can state
internally. If we have a pointed equivalence α : A <~>* B, we can turn it into an equivalence
γ : (B ->* X) <~>* (A ->* X), natural in X. Naturality means that if we have f : X -> X' then we
can fill the following square (using a pointed homotopy)
(B ->* X)  --> (A ->* X)
  |             |
  v             v
(B ->* X') --> (B ->* X')
such that if f is the constant map, then this square is equal to the canonical filler of that
square (where the fact that f is constant is used).

Conversely, if we have such a γ natural in X, we can obtain an equivalence A <~>* B.
Moreover, these operations are equivalences in the sense that going from α to γ to α is the
same as doing nothing, and going from γ to α to γ is the same as doing nothing. However, we
need higher coherences for γ to show that the proof of naturality is the same, which we didn't do.

Author: Floris van Doorn (informal proofs in collaboration with Stefano Piceghello)
*)

import .pointed

open equiv is_equiv eq
namespace pointed

  universe variable u

Definition ppcompose_right_ppcompose_left {A A' B B' : pType} (f : A ->* A') (g : B ->* B'):
  psquare (ppcompose_right f) (ppcompose_right f) (ppcompose_left g) (ppcompose_left g).
  ptranspose !ppcompose_left_ppcompose_right


Definition pyoneda_weak {A B : pType.{u}} (γ : forall (X : pType.{u}), ppMap B X <~>* ppMap A X)
  (p : forall (X X' : pType) (f : X ->* X') (g : B ->* X), f o* γ X g ==* γ X' (f o* g)) : A <~>* B.
Proof.
  fapply pequiv.MK,
  { exact γ B (pid B) },
  { exact (γ A)^-1ᵉ* (pid A) },
  { refine p _ _ @* _,
  exact pap (γ A) !pcompose_pid @* phomotopy_path (to_right_inv (γ A) _) },
  {             exact sorry
  }
Defined.

Definition pyoneda {A B : pType.{u}} (γ : forall (X : pType.{u}), ppMap B X <~>* ppMap A X)
  (p : forall (X X' : pType) (f : X ->* X'), psquare (γ X) (γ X') (ppcompose_left f) (ppcompose_left f))
  : A <~>* B.
Proof.
  fapply pequiv.MK,
  { exact γ B (pid B) },
  { exact (γ A)^-1ᵉ* (pid A) },
  { refine phomotopy_path (p _ _) @* _,
  exact pap (γ A) !pcompose_pid @* phomotopy_path (to_right_inv (γ A) _) },
  { refine phomotopy_path ((p _)^-1ʰ* _) @* _,
  exact pap (γ B)^-1ᵉ* !pcompose_pid @* phomotopy_path (to_left_inv (γ B) _) }
Defined.

Definition pyoneda_right_inv {A B : pType.{u}} (α : A <~>* B) :
  pyoneda (fun X => ppMap_pequiv_ppMap_left α) (fun X X' f => proof !ppcompose_right_ppcompose_left qed) ==*
  α.
  Build_pHomotopy homotopy.rfl idp

Definition pyoneda_left_inv {A B : pType.{u}} (γ : forall (X : pType.{u}), ppMap B X <~>* ppMap A X)
  (p : forall (X X' : pType) (f : X ->* X'), psquare (γ X) (γ X') (ppcompose_left f) (ppcompose_left f))
  (H : forall (X) (X' : pType) (g : B ->* X), phomotopy_path (p (pconst X X') g) =
  !pconst_pcompose @* (pap (γ X') !pconst_pcompose @* phomotopy_path (point_eq (γ X')))^-1*)
  (X : pType) : ppcompose_right (pyoneda γ p) ==* γ X.
 begin
  fapply phomotopy_mk_ppMap,
  { intro f, refine phomotopy_path (p _ _) @* _, exact pap (γ X) !pcompose_pid },
  { refine _ @ !phomotopy_path_of_phomotopy^-1,
  refine !trans_assoc @ _,
  refine H X (pid B) ◾** idp @ !trans_assoc @ idp ◾** _ @ !trans_refl,
  apply trans_left_inv }
Defined.

Definition pyoneda_weak_left_inv {A B : pType.{u}} (γ : forall (X : pType.{u}), ppMap B X <~>* ppMap A X)
  (p : forall (X : pType) (X' : pType) (g : B ->* X), ppcompose_right (γ X g) ==* γ X' o* ppcompose_right g)
  (X : pType) : ppcompose_right (pyoneda_weak γ (fun X X' f g => phomotopy_path (p X' g f))) ==* γ X.
Proof.
  fapply phomotopy_mk_ppMap,
  { intro f, refine phomotopy_path (p _ _ _) @* _, exact pap (γ X) !pcompose_pid },
  { refine _ @ !phomotopy_path_of_phomotopy^-1,
  refine !trans_assoc @ _,
  refine (ap phomotopy_path (eq_con_inv_of_con_eq (point_htpy (p X (pid B)))) @
  !phomotopy_path_con @ !phomotopy_path_of_phomotopy ◾**
  (!phomotopy_path_inv @ (!phomotopy_path_con @ (!phomotopy_path_ap @
  ap (pap' _) !phomotopy_path_of_phomotopy) ◾** idp)⁻²**)) ◾** idp @ _,
  refine !trans_assoc @ idp ◾** _ @ !trans_refl,
  apply trans_left_inv }
Defined.


Defined. pointed
