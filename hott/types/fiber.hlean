(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Mike Shulman

Ported from Coq HoTT
Theorems about fibers
*)

import .sigma .eq .pi cubical.squareover .pointed .eq
open equiv sigma sigma.ops eq pi pointed is_equiv

structure fiber {A B : Type} (f : A -> B) (b : B).
  (point : A)
  (point_eq : f point = b)

namespace fiber
  variables {A B : Type} {f : A -> B} {b : B}

  protectedDefinition sigma_char
    (f : A -> B) (b : B) : fiber f b <~> (Σ(a : A), f a = b).
Proof.
  fapply equiv.MK,
    {intro x, exact ⟨point x, point_eq x⟩},
    {intro x, exact (fiber.mk x.1 x.2)},
    {intro x, cases x, apply idp },
    {intro x, cases x, apply idp },
Defined.

Definition fiber_eq_equiv (x y : fiber f b)
    : (x = y) <~> (Σ(p : point x = point y), point_eq x = ap f p @ point_eq y).
Proof.
    apply equiv.trans,
      apply eq_equiv_fn_eq_of_equiv, apply fiber.sigma_char,
    apply equiv.trans,
      apply sigma_eq_equiv,
    apply sigma_equiv_sigma_right,
    intro p,
    apply eq_pathover_equiv_Fl,
Defined.

Definition fiber_eq {x y : fiber f b} (p : point x = point y)
    (q : point_eq x = ap f p @ point_eq y) : x = y.
  to_inv !fiber_eq_equiv ⟨p, q⟩

Definition fiber_pathover {X : Type} {A B : X -> Type} {x₁ x₂ : X} {p : x₁ = x₂}
    {f : forall x, A x -> B x} {b : forall x, B x} {v₁ : fiber (f x₁) (b x₁)} {v₂ : fiber (f x₂) (b x₂)}
    (q : point v₁ =[p] point v₂)
    (r : squareover B hrfl (pathover_idp_of_eq (point_eq v₁)) (pathover_idp_of_eq (point_eq v₂))
                           (apo f q) (apd b p))
    : v₁ =[p] v₂.
Proof.
    apply pathover_of_fn_pathover_fn (fun a => !fiber.sigma_char), esimp,
    fapply sigma_pathover: esimp,
    { exact q},
    { induction v₁ with a₁ p₁, induction v₂ with a₂ p₂, esimp at *, induction q, esimp at *,
      apply pathover_idp_of_eq, apply eq_of_vdeg_square, apply square_of_squareover_ids r}
Defined.

  open is_trunc
Definition fiber_pr1 (B : A -> Type) (a : A) : fiber (pr1 : (Σa, B a) -> A) a <~> B a.
  calc
    fiber pr1 a <~> Σu, u.1 = a            : fiber.sigma_char
            ... <~> Σa' (b : B a'), a' = a : sigma_assoc_equiv
            ... <~> Σa' (p : a' = a), B a' : sigma_equiv_sigma_right (fun a' => !comm_equiv_nondep)
            ... <~> Σu, B u.1              : sigma_assoc_equiv
            ... <~> B a                    : !sigma_equiv_of_is_contr_left

Definition sigma_fiber_equiv (f : A -> B) : (Σb, fiber f b) <~> A.
  calc
    (Σb, fiber f b) <~> Σb a, f a = b : sigma_equiv_sigma_right (fun b => !fiber.sigma_char)
                ... <~> Σa b, f a = b : sigma_comm_equiv
                ... <~> A             : sigma_equiv_of_is_contr_right

Definition is_pointed_fiber [instance] (f : A -> B) (a : A)
    : pointed (fiber f (f a)).
  pointed.mk (fiber.mk a idp)

Definition pointed_fiber (f : A -> B) (a : A) : pType.
  pointed.Mk (fiber.mk a (idpath (f a)))

Definition is_trunc_fun (n : ℕ₋₂) (f : A -> B).
  forall (b : B), is_trunc n (fiber f b)

Definition is_contr_fun (f : A -> B) . is_trunc_fun -2 f

  (* pre and post composition with equivalences *)
  open function
  variable (f)
  protectedDefinition equiv_postcompose {B' : Type} (g : B <~> B') --[H : is_equiv g]
    (b : B) : fiber (g o f) (g b) <~> fiber f b.
  calc
    fiber (g o f) (g b) <~> Σa : A, g (f a) = g b : fiber.sigma_char
                    ... <~> Σa : A, f a = b       : begin
                                                    apply sigma_equiv_sigma_right, intro a,
                                                    apply equiv.symm, apply eq_equiv_fn_eq
                                                  end
                    ... <~> fiber f b             : fiber.sigma_char

  protectedDefinition equiv_precompose {A' : Type} (g : A' <~> A) --[H : is_equiv g]
    (b : B) : fiber (f o g) b <~> fiber f b.
  calc
    fiber (f o g) b <~> Σa' : A', f (g a') = b   : fiber.sigma_char
                ... <~> Σa : A, f a = b          : begin
                                                   apply sigma_equiv_sigma g,
                                                   intro a', apply erfl
                                                 end
                ... <~> fiber f b                : fiber.sigma_char

Defined. fiber

open unit is_trunc pointed

namespace fiber

Definition fiber_star_equiv (A : Type) : fiber (fun x : A => star) star <~> A.
Proof.
    fapply equiv.MK,
    { intro f, cases f with a H, exact a },
    { intro a, apply fiber.mk a, reflexivity },
    { intro a, reflexivity },
    { intro f, cases f with a H, change fiber.mk a (refl star) = fiber.mk a H,
      rewrite [is_set.elim H (refl star)] }
Defined.

Definition fiber_const_equiv (A : Type) (a₀ : A) (a : A)
    : fiber (fun z : unit => a₀) a <~> a₀ = a.
  calc
    fiber (fun z : unit => a₀) a
      <~> Σz : unit, a₀ = a : fiber.sigma_char
  ... <~> a₀ = a : sigma_unit_left

  (* the pointed fiber of a pointed map, which is the fiber over the basepoint *)
  open pointed
Definition pfiber {X Y : pType} (f : X ->* Y) : pType.
  pointed.MK (fiber f (point _)) (fiber.mk (point _) !point_eq)

Definition ppoint {X Y : pType} (f : X ->* Y) : pfiber f ->* X.
  Build_pMap point idp

Definition pfiber.sigma_char {A B : pType} (f : A ->* B)
    : pfiber f <~>* pointed.MK (Σa, f a = (point _)) ⟨(point _), point_eq f⟩.
  pequiv_of_equiv (fiber.sigma_char f (point _)) idp

Definition ppoint_sigma_char {A B : pType} (f : A ->* B)
    : ppoint f ==* Build_pMap pr1 idp o* pfiber.sigma_char f.
  !reflexivity

Definition pfiber_pequiv_of_phomotopy {A B : pType} {f g : A ->* B} (h : f ==* g)
    : pfiber f <~>* pfiber g.
Proof.
    fapply pequiv_of_equiv,
    { refine (fiber.sigma_char f (point _) @e _ @e (fiber.sigma_char g (point _))^-1ᵉ),
      apply sigma_equiv_sigma_right, intros a,
      apply equiv_eq_closed_left, apply (to_homotopy h) },
    { refine (fiber_eq rfl _),
      change (h (point _))^-1 @ point_eq f = idp @ point_eq g,
      rewrite idp_con, apply inv_con_eq_of_eq_con, symmetry, exact (point_htpy h) }
Defined.

Definition transport_fiber_equiv {A B : Type} (f : A -> B) {b1 b2 : B} (p : b1 = b2)
    : fiber f b1 <~> fiber f b2.
    calc fiber f b1 <~> Σa, f a = b1 : fiber.sigma_char
               ...  <~> Σa, f a = b2 : sigma_equiv_sigma_right (fun a => equiv_eq_closed_right (f a) p)
               ...  <~> fiber f b2   : fiber.sigma_char

Definition pequiv_postcompose {A B B' : pType} (f : A ->* B) (g : B <~>* B')
    : pfiber (g o* f) <~>* pfiber f.
Proof.
    fapply pequiv_of_equiv, esimp,
    refine transport_fiber_equiv (g o* f) (point_eq g)^-1 @e fiber.equiv_postcompose f g (Point B),
    esimp, apply (ap (fiber.mk (Point A))), refine (concat_pp_p _ _ _) @ _, apply inv_con_eq_of_eq_con,
    rewrite [▸*, con.assoc, con.right_inv, con_idp, -ap_compose'],
    exact ap_con_eq_con (fun x => ap g^-1ᵉ* (ap g (pleft_inv' g x)^-1) @ ap g^-1ᵉ* (pright_inv g (g x)) @
      pleft_inv' g x) (point_eq f)
Defined.

Definition pequiv_precompose {A A' B : pType} (f : A ->* B) (g : A' <~>* A)
    : pfiber (f o* g) <~>* pfiber f.
Proof.
    fapply pequiv_of_equiv, esimp,
    refine fiber.equiv_precompose f g (Point B),
    esimp, apply (eq_of_fn_eq_fn (fiber.sigma_char _ _)), fapply sigma_eq: esimp,
    { apply point_eq g },
    { apply eq_pathover_Fl' }
Defined.

Definition pfiber_pequiv_of_square {A B C D : pType} {f : A ->* B} {g : C ->* D} (h : A <~>* C)
    (k : B <~>* D) (s : k o* f ==* g o* h) : pfiber f <~>* pfiber g.
    calc pfiber f <~>* pfiber (k o* f) : pequiv_postcompose
              ... <~>* pfiber (g o* h) : pfiber_pequiv_of_phomotopy s
              ... <~>* pfiber g : pequiv_precompose

Definition pcompose_ppoint {A B : pType} (f : A ->* B) : f o* ppoint f ==* pconst (pfiber f) B.
Proof.
    fapply Build_pHomotopy,
    { exact point_eq },
    { exact (concat_1p _)^-1 }
Defined.

Definition point_fiber_eq {A B : Type} {f : A -> B} {b : B} {x y : fiber f b}
    (p : point x = point y) (q : point_eq x = ap f p @ point_eq y) :
    ap point (fiber_eq p q) = p.
Proof.
    induction x with a r, induction y with a' s, esimp at *, induction p,
    induction q using eq.rec_symm, induction s, reflexivity
Defined.

Definition fiber_eq_equiv_fiber {A B : Type} {f : A -> B} {b : B} (x y : fiber f b) :
    x = y <~> fiber (ap1_gen f (point_eq x) (point_eq y)) (idpath b).
  calc
    x = y <~> fiber.sigma_char f b x = fiber.sigma_char f b y :
      eq_equiv_fn_eq_of_equiv (fiber.sigma_char f b) x y
      ... <~> Σ(p : point x = point y), point_eq x =[p] point_eq y : sigma_eq_equiv
      ... <~> Σ(p : point x = point y), (point_eq x)^-1 @ ap f p @ point_eq y = idp :
      sigma_equiv_sigma_right (fun p =>
      calc point_eq x =[p] point_eq y <~> point_eq x = ap f p @ point_eq y : eq_pathover_equiv_Fl
           ... <~> ap f p @ point_eq y = point_eq x : eq_equiv_eq_symm
           ... <~> (point_eq x)^-1 @ (ap f p @ point_eq y) = idp : eq_equiv_inv_con_eq_idp
           ... <~> (point_eq x)^-1 @ ap f p @ point_eq y = idp : equiv_eq_closed_left _ (concat_pp_p _ _ _)^-1)
      ... <~> fiber (ap1_gen f (point_eq x) (point_eq y)) (idpath b) : fiber.sigma_char

Definition loop_pfiber {A B : pType} (f : A ->* B) : loops (pfiber f) <~>* pfiber (Ω-> f).
  pequiv_of_equiv (fiber_eq_equiv_fiber (point _) pt)
    begin
      induction f with f f₀, induction B with B b₀, esimp at (f,f₀), induction f₀, reflexivity
    end

Definition pfiber_loop_space {A B : pType} (f : A ->* B) : pfiber (Ω-> f) <~>* loops (pfiber f).
  (loop_pfiber f)^-1ᵉ*

Definition point_fiber_eq_equiv_fiber {A B : Type} {f : A -> B} {b : B} {x y : fiber f b}
    (p : x = y) : point (fiber_eq_equiv_fiber x y p) = ap1_gen point idp idp p.
  by induction p; reflexivity

  lemma ppoint_loop_pfiber {A B : pType} (f : A ->* B) :
    ppoint (Ω-> f) o* loop_pfiber f ==* Ω-> (ppoint f).
  Build_pHomotopy (point_fiber_eq_equiv_fiber)
    begin
     induction f with f f₀, induction B with B b₀, esimp at (f,f₀), induction f₀, reflexivity
    end

  lemma ppoint_loop_pfiber_inv {A B : pType} (f : A ->* B) :
    Ω-> (ppoint f) o* (loop_pfiber f)^-1ᵉ* ==* ppoint (Ω-> f).
  (phomotopy_pinv_right_of_phomotopy (ppoint_loop_pfiber f))^-1*

  lemma pfiber_pequiv_of_phomotopy_ppoint {A B : pType} {f g : A ->* B} (h : f ==* g)
    : ppoint g o* pfiber_pequiv_of_phomotopy h ==* ppoint f.
Proof.
    induction f with f f₀, induction g with g g₀, induction h with h h₀, induction B with B b₀,
    esimp at *, induction h₀, induction g₀,
    fapply Build_pHomotopy,
    { reflexivity },
    { symmetry, rexact point_fiber_eq (idpath (point _))
        (inv_con_eq_of_eq_con (idpath (h (point _) @ (idp @ point_eq (fiber.mk (point _) idp))))) }
Defined.

  lemma pequiv_postcompose_ppoint {A B B' : pType} (f : A ->* B) (g : B <~>* B')
    : ppoint f o* fiber.pequiv_postcompose f g ==* ppoint (g o* f).
Proof.
    induction f with f f₀, induction g with g hg g₀, induction B with B b₀,
    induction B' with B' b₀', esimp at * ⊢, induction g₀, induction f₀,
    fapply Build_pHomotopy,
    { reflexivity },
    { symmetry,
      refine !ap_compose^-1 @ _, apply ap_constant }
Defined.

  lemma pequiv_precompose_ppoint {A A' B : pType} (f : A ->* B) (g : A' <~>* A)
    : ppoint f o* fiber.pequiv_precompose f g ==* g o* ppoint (f o* g).
Proof.
    induction f with f f₀, induction g with g h₁ h₂ p₁ p₂, induction B with B b₀,
    induction g with g g₀, induction A with A a₀', esimp at *, induction g₀, induction f₀,
    reflexivity
Defined.

Definition pfiber_pequiv_of_square_ppoint {A B C D : pType} {f : A ->* B} {g : C ->* D}
    (h : A <~>* C) (k : B <~>* D) (s : k o* f ==* g o* h)
    : ppoint g o* pfiber_pequiv_of_square h k s ==* h o* ppoint f.
Proof.
    refine !passoc^-1* @* _,
    refine pwhisker_right _ !pequiv_precompose_ppoint @* _,
    refine !passoc @* _,
    apply pwhisker_left,
    refine !passoc^-1* @* _,
    refine pwhisker_right _ !pfiber_pequiv_of_phomotopy_ppoint @* _,
    apply pinv_right_phomotopy_of_phomotopy,
    refine !pequiv_postcompose_ppoint^-1*,
Defined.

  (* this breaks certain proofs if it is an instance *)
Definition is_trunc_fiber (n : ℕ₋₂) {A B : Type} (f : A -> B) (b : B)
    [is_trunc n A] [is_trunc (n.+1) B] : is_trunc n (fiber f b).
  is_trunc_equiv_closed_rev n !fiber.sigma_char

Definition is_trunc_pfiber (n : ℕ₋₂) {A B : pType} (f : A ->* B)
    [is_trunc n A] [is_trunc (n.+1) B] : is_trunc n (pfiber f).
  is_trunc_fiber n f pt

Definition fiber_equiv_of_is_contr {A B : Type} (f : A -> B) (b : B) [is_contr B] :
    fiber f b <~> A.
  !fiber.sigma_char @e !sigma_equiv_of_is_contr_right

Definition pfiber_pequiv_of_is_contr {A B : pType} (f : A ->* B) [is_contr B] :
    pfiber f <~>* A.
  pequiv_of_equiv (fiber_equiv_of_is_contr f (point _)) idp

Definition pfiber_ppoint_equiv {A B : pType} (f : A ->* B) : pfiber (ppoint f) <~> loops B.
  calc
    pfiber (ppoint f) <~> Σ(x : pfiber f), ppoint f x = (point _) : fiber.sigma_char
      ... <~> Σ(x : Σa, f a = (point _)), x.1 = (point _) : by exact sigma_equiv_sigma !fiber.sigma_char (fun a => erfl)
      ... <~> Σ(x : Σa, a = (point _)), f x.1 = (point _) : by exact !sigma_assoc_comm_equiv
      ... <~> f (point _) = (point _) : by exact !sigma_equiv_of_is_contr_left
      ... <~> loops B : by exact !equiv_eq_closed_left !point_eq

Definition pfiber_ppoint_pequiv {A B : pType} (f : A ->* B) : pfiber (ppoint f) <~>* loops B.
  pequiv_of_equiv (pfiber_ppoint_equiv f) (con_Vp _)

Definition fiber_ppoint_equiv_eq {A B : pType} {f : A ->* B} {a : A} (p : f a = (point _))
    (q : ppoint f (fiber.mk a p) = (point _)) :
    pfiber_ppoint_equiv f (fiber.mk (fiber.mk a p) q) = (point_eq f)^-1 @ ap f q^-1 @ p.
Proof.
    refine _ @ (concat_pp_p _ _ _)^-1,
    apply whisker_left,
    refine eq_transport_Fl _ _ @ _,
    apply whisker_right,
    refine inverse2 !ap_inv @ !inv_inv @ _,
    refine ap_compose f pr₁ _ @ ap02 f !ap_pr1_center_eq_sigma_eq',
Defined.

Definition fiber_ppoint_equiv_inv_eq {A B : pType} (f : A ->* B) (p : loops B) :
    (pfiber_ppoint_equiv f)^-1ᵉ p = fiber.mk (fiber.mk (point _) (point_eq f @ p)) idp.
Proof.
    apply inv_eq_of_eq,
    refine _ @ !fiber_ppoint_equiv_eq^-1,
    exact !inv_con_cancel_left^-1
Defined.


Defined. fiber

open function is_equiv

namespace fiber
  (* Theorem 4.7.6 *)
  variables {A : Type} {P Q : A -> Type}
  variable (f : forall a, P a -> Q a)

Definition fiber_total_equiv {a : A} (q : Q a)
    : fiber (total f) ⟨a , q⟩ <~> fiber (f a) q.
  calc
    fiber (total f) ⟨a , q⟩
          <~> Σ(w : Σx, P x), ⟨w.1 , f w.1 w.2 ⟩ = ⟨a , q⟩
            : fiber.sigma_char
      ... <~> Σ(x : A), Σ(p : P x), ⟨x , f x p⟩ = ⟨a , q⟩
            : sigma_assoc_equiv
      ... <~> Σ(x : A), Σ(p : P x), Σ(H : x = a), f x p =[H] q
            :
            begin
              apply sigma_equiv_sigma_right, intro x,
              apply sigma_equiv_sigma_right, intro p,
              apply sigma_eq_equiv
            end
      ... <~> Σ(x : A), Σ(H : x = a), Σ(p : P x), f x p =[H] q
            :
            begin
              apply sigma_equiv_sigma_right, intro x,
              apply sigma_comm_equiv
            end
      ... <~> Σ(w : Σx, x = a), Σ(p : P w.1), f w.1 p =[w.2] q
            : sigma_assoc_equiv
      ... <~> Σ(p : P (center (Σx, x=a)).1), f (center (Σx, x=a)).1 p =[(center (Σx, x=a)).2] q
            : sigma_equiv_of_is_contr_left
      ... <~> Σ(p : P a), f a p =[idpath a] q
            : equiv_of_eq idp
      ... <~> Σ(p : P a), f a p = q
            :
            begin
              apply sigma_equiv_sigma_right, intro p,
              apply pathover_idp
            end
      ... <~> fiber (f a) q
            : fiber.sigma_char

Defined. fiber
