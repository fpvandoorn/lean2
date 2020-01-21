(*
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Favonia

The Wedge Sum of a family of Pointed Types
*)
import homotopy.wedge ..move_to_lib ..choice ..pointed_pi

open eq is_equiv pushout pointed unit trunc_index sigma bool equiv choice unit is_trunc sigma.ops lift function pi prod

Definition fwedge' {I : Type} (F : I -> pType) : Type . pushout (fun i => ⟨i, Point (F i)⟩) (fun i => ⋆)
Definition (point _)' {I : Type} {F : I -> pType} : fwedge' F . inr ⋆
Definition fwedge {I : Type} (F : I -> pType) : pType . pointed.MK (fwedge' F) (point _)'

notation `⋁` . fwedge

namespace fwedge
  variables {I : Type} {F : I -> pType}

Definition il {i : I} (x : F i) : ⋁F . inl ⟨i, x⟩
Definition inl (i : I) (x : F i) : ⋁F . il x
Definition pinl (i : I) : F i ->* ⋁F . Build_pMap (inl i) (glue i)
Definition glue (i : I) : inl i (point _) = (point _) :> ⋁ F . glue i

  protectedDefinition rec {P : ⋁F -> Type} (Pinl : forall (i : I) (x : F i), P (il x))
  (Pinr : P (point _)) (Pglue : forall i, pathover P (Pinl i (point _)) (glue i) (Pinr)) (y : fwedge' F) : P y.
Proof. induction y, induction x, apply Pinl, induction x, apply Pinr, apply Pglue end

  protectedDefinition elim {P : Type} (Pinl : forall (i : I) (x : F i), P)
  (Pinr : P) (Pglue : forall i, Pinl i (point _) = Pinr) (y : fwedge' F) : P.
Proof. induction y with x u, induction x with i x, exact Pinl i x, induction u, apply Pinr, apply Pglue end

  protectedDefinition elim_glue {P : Type} {Pinl : forall (i : I) (x : F i), P}
  {Pinr : P} (Pglue : forall i, Pinl i (point _) = Pinr) (i : I)
  : ap (fwedge.elim Pinl Pinr Pglue) (fwedge.glue i) = Pglue i.
  !pushout.elim_glue

  protectedDefinition rec_glue {P : ⋁F -> Type} {Pinl : forall (i : I) (x : F i), P (il x)}
  {Pinr : P (point _)} (Pglue : forall i, pathover P (Pinl i (point _)) (glue i) (Pinr)) (i : I)
  : apd (fwedge.rec Pinl Pinr Pglue) (fwedge.glue i) = Pglue i.
  !pushout.rec_glue

Defined. fwedge




namespace fwedge

Definition fwedge_of_wedge {A B : pType} (x : A ∨ B) : ⋁(bool.rec A B).
Proof.
  induction x with a b,
  { exact inl ff a },
  { exact inl tt b },
  { exact glue ff @ (glue tt)^-1 }
Defined.

Definition wedge_of_fwedge {A B : pType} (x : ⋁(bool.rec A B)) : A ∨ B.
Proof.
  induction x with b x b,
  { induction b, exact pushout.inl x, exact pushout.inr x },
  { exact pushout.inr (point _) },
  { induction b, exact pushout.glue ⋆, reflexivity }
Defined.

Definition wedge_pequiv_fwedge (A B : pType) : A ∨ B <~>* ⋁(bool.rec A B).
Proof.
  fapply pequiv_of_equiv,
  { fapply equiv.MK,
  { exact fwedge_of_wedge },
  { exact wedge_of_fwedge },
  { exact abstract begin intro x, induction x with b x b,
  { induction b: reflexivity },
  { exact glue tt },
  { apply eq_pathover_id_right,
  refine ap_compose fwedge_of_wedge _ _ @ ap02 _ !elim_glue @ph _,
  induction b, exact !elim_glue @ph whisker_bl _ hrfl, apply square_of_eq idp }
Defined. end },
  { exact abstract begin intro x, induction x with a b,
  { reflexivity },
  { reflexivity },
  { apply eq_pathover_id_right,
  refine ap_compose wedge_of_fwedge _ _ @ ap02 _ !elim_glue @ (ap_pp _ _ _) @
  !elim_glue ◾ (!ap_inv @ !elim_glue⁻²) @ph _, exact hrfl } end end}},
  { exact glue ff }
Defined.

Definition is_contr_fwedge_of_neg {I : Type} (P : I -> pType) (H : ¬ I) : is_contr (⋁P).
Proof.
  apply is_contr.mk (point _), intro x, induction x, contradiction, reflexivity, contradiction
Defined.

Definition is_contr_fwedge_empty [instance] : is_contr (⋁empty.elim).
  is_contr_fwedge_of_neg _ id

Definition fwedge_pmap {I : Type} {F : I -> pType} {X : pType} (f : forall i, F i ->* X) : ⋁F ->* X.
Proof.
  fapply Build_pMap,
  { intro x, induction x,
  exact f i x,
  exact (point _),
  exact point_eq (f i) },
  { reflexivity }
Defined.

Definition wedge_pmap {A B : pType} {X : pType} (f : A ->* X) (g : B ->* X) : (A ∨ B) ->* X.
Proof.
  fapply Build_pMap,
  { intro x, induction x, exact (f a), exact (g a), exact (point_eq (f) @ (point_eq g)^-1) },
  { exact point_eq f }
Defined.

Definition fwedge_pmap_beta {I : Type} {F : I -> pType} {X : pType} (f : forall i, F i ->* X) (i : I) :
  fwedge_pmap f o* pinl i ==* f i.
Proof.
  fapply Build_pHomotopy,
  { reflexivity },
  { exact (concat_1p _) @ !fwedge.elim_glue^-1 }
Defined.

Definition fwedge_pmap_eta {I : Type} {F : I -> pType} {X : pType} (g : ⋁F ->* X) :
  fwedge_pmap (fun i => g o* pinl i) ==* g.
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x,
  reflexivity,
  exact (point_eq g)^-1,
  apply eq_pathover, refine !elim_glue @ph _, apply whisker_lb, exact hrfl },
  { exact con.left_inv (point_eq g) }
Defined.

Definition fwedge_pmap_pinl {I : Type} {F : I -> pType} : fwedge_pmap (fun i => pinl i) ==* pid (⋁ F).
Proof.
  fapply Build_pHomotopy,
  { intro x, induction x,
  reflexivity, reflexivity,
  apply eq_pathover, apply hdeg_square, refine !elim_glue @ !ap_id^-1 },
  { reflexivity }
Defined.

Definition fwedge_pmap_equiv {I : Type} (F : I -> pType) (X : pType) :
  ⋁F ->* X <~> forall i, F i ->* X.
Proof.
  fapply equiv.MK,
  { intro g i, exact g o* pinl i },
  { exact fwedge_pmap },
  { intro f, apply eq_of_homotopy, intro i, apply path_pforall, apply fwedge_pmap_beta f i },
  { intro g, apply path_pforall, exact fwedge_pmap_eta g }
Defined.

Definition wedge_pmap_equiv  (A B X : pType) :
  ((A ∨ B) ->* X) <~> ((A ->* X) \* (B ->* X)).
  calc (A ∨ B) ->* X <~> ⋁(bool.rec A B) ->* X : by exact ppMap_pequiv_ppMap_left (wedge_pequiv_fwedge A B)^-1ᵉ*
  ...       <~> forall i, (bool.rec A B) i ->* X : by exact fwedge_pmap_equiv (bool.rec A B) X
  ...       <~>  (A ->* X) \* (B ->* X) : by exact pi_bool_left (fun i => bool.rec A B i ->* X)


Definition fwedge_pmap_nat₂ {I : Type}(F : I -> pType){X Y : pType}
  (f : X ->* Y) (h : forall i, F i ->* X) (w : fwedge F) :
  (f o* (fwedge_pmap h)) w = fwedge_pmap (fun i => f o* (h i)) w.
Proof.
  induction w, reflexivity,
  refine !point_eq,
  apply eq_pathover,
  refine ap_compose f (fwedge_pmap h) _ @ph _,
  refine ap (ap f) !elim_glue @ph _,
  refine _ @hp !elim_glue^-1, esimp,
  apply whisker_br,
  apply !hrefl
Defined.


Definition prod_pi_bool_comp_funct {A B : pType}(X : pType) : (A ->* X) \* (B ->* X) -> forall , (bool.rec A B u ->* X).
Proof.
  refine equiv.symm _,
  fapply pi_bool_left
Defined.

Definition prod_funct_comp {A B X Y : pType} (f : X ->* Y) : (A ->* X) \* (B ->* X) -> (A ->* Y) \* (B ->* Y).
  prod_functor (pcompose f) (pcompose f)

Definition left_comp_pi_bool_funct {A B X Y : pType} (f : X ->* Y) : (forall , (bool.rec A B u ->* X)) ->  (forall u, (bool.rec A B u ->* Y)).
Proof.
  intro, intro, exact f o* (a u)
Defined.

Definition left_comp_pi_bool {A B X Y : pType} (f : X ->* Y) : forall u, ((bool.rec A B u ->* X) ->  (bool.rec A B u ->* Y)).
Proof.
  intro, intro, exact fo* a
Defined.

Definition prod_to_pi_bool_nat_square {A B X Y : pType} (f : X ->* Y) :
  hsquare (prod_pi_bool_comp_funct X) (prod_pi_bool_comp_funct Y) (prod_funct_comp f) (@left_comp_pi_bool_funct A B X Y f).
Proof.
  intro x, fapply eq_of_homotopy, intro u, induction u, esimp, esimp
Defined.

Definition fwedge_pmap_nat_square {A B X Y : pType} (f : X ->* Y) :
  hsquare (fwedge_pmap_equiv (bool.rec A B) X)^-1ᵉ (fwedge_pmap_equiv (bool.rec A B) Y)^-1ᵉ (left_comp_pi_bool_funct f) (pcompose f).
Proof.
  intro h, esimp, fapply path_pforall, fapply Build_pHomotopy,
  exact fwedge_pmap_nat₂ (fun u => bool.rec A B u) f h,
  reflexivity
Defined.

Definition fwedge_to_wedge_nat_square {A B X Y : pType} (f : X ->* Y) :
  hsquare (ppMap_pequiv_ppMap_left (wedge_pequiv_fwedge A B)) (ppMap_pequiv_ppMap_left (wedge_pequiv_fwedge A B)) (pcompose f) (pcompose f).
Proof.
  exact sorry
Defined.

Definition wedge_pmap_nat₂ (A B X Y : pType) (f : X ->* Y) (h : A ->* X) (k : B ->* X) : forall (w : A ∨ B),
  (f o* (wedge_pmap h k)) w = wedge_pmap (f o* h )(f o* k) w .
have H : _, from
  (@prod_to_pi_bool_nat_square A B X Y f) @htyh (fwedge_pmap_nat_square f) @htyh (fwedge_to_wedge_nat_square f),
sorry


Definition fwedge_pmap_phomotopy {I : Type} {F : I -> pType} {X : pType} {f g : forall i, F i ->* X}
  (h : forall i, f i ==* g i) : fwedge_pmap f ==* fwedge_pmap g.
Proof.
  fconstructor,
  { fapply fwedge.rec,
  { exact h },
  { reflexivity },
  { intro i, apply eq_pathover,
  refine _ @ph _ @hp _,
  { exact (point_eq (g i)) },
  { exact (point_eq (f i)) },
  { exact !elim_glue },
  { apply square_of_eq,
  exact ((phomotopy.sigma_char (f i) (g i)) (h i)).2
  },
  { refine !elim_glue^-1 }
  }
  },
  { reflexivity }
Defined.

  open trunc
Definition trunc_fwedge_pmap_equiv.{u v w} {n : ℕ₋₂} {I : Type.{u}} (H : has_choice n I)
  (F : I -> pType.{v}) (X : pType.{w}) : trunc n (⋁F ->* X) <~> forall i, trunc n (F i ->* X).
  trunc_equiv_trunc n (fwedge_pmap_equiv F X) @e choice_equiv (fun i => F i ->* X)

Definition fwedge_functor {I : Type} {F F' : I -> pType} (f : forall , F i ->* F' i)
  : ⋁ F ->* ⋁ F' . fwedge_pmap (fun i => pinl i o* f i)

Definition fwedge_functor_pid {I : Type} {F : I -> pType}
  : @fwedge_functor I F F (fun i => !pid) ==* !pid.
  calc fwedge_pmap (fun i => pinl i o* !pid) ==* fwedge_pmap pinl : by exact fwedge_pmap_phomotopy (fun i => pcompose_pid (pinl i))
  ... ==* fwedge_pmap (fun i => !pid o* pinl i) : by exact fwedge_pmap_phomotopy (fun i => phomotopy.symm (pid_pcompose (pinl i)))
  ... ==* !pid : by exact fwedge_pmap_eta !pid

Definition fwedge_functor_pcompose {I : Type} {F F' F'' : I -> pType} (g : forall , F' i ->* F'' i)
  (f : forall i, F i ->* F' i) : fwedge_functor (fun i => g i o* f i) ==* fwedge_functor g o* fwedge_functor f.
  calc        fwedge_functor (fun i => g i o* f i)
  ==* fwedge_pmap (fun i => (pinl i o* g i) o* f i)
  : by exact fwedge_pmap_phomotopy (fun i => phomotopy.symm (passoc (pinl i) (g i) (f i)))
  ... ==* fwedge_pmap (fun i => (fwedge_functor g o* pinl i) o* f i)
  : by exact fwedge_pmap_phomotopy (fun i => pwhisker_right (f i) (phomotopy.symm (fwedge_pmap_beta (fun i => pinl i o* g i) i)))
  ... ==* fwedge_pmap (fun i => fwedge_functor g o* (pinl i o* f i))
  : by exact fwedge_pmap_phomotopy (fun i => passoc (fwedge_functor g) (pinl i) (f i))
  ... ==* fwedge_pmap (fun i => fwedge_functor g o* (fwedge_functor f o* pinl i))
  : by exact fwedge_pmap_phomotopy (fun i => pwhisker_left (fwedge_functor g) (phomotopy.symm (fwedge_pmap_beta (fun i => pinl i o* f i) i)))
  ... ==* fwedge_pmap (fun i => (fwedge_functor g o* fwedge_functor f) o* pinl i)
  : by exact fwedge_pmap_phomotopy (fun i => (phomotopy.symm (passoc (fwedge_functor g) (fwedge_functor f) (pinl i))))
  ... ==* fwedge_functor g o* fwedge_functor f
  : by exact fwedge_pmap_eta (fwedge_functor g o* fwedge_functor f)

Definition fwedge_functor_phomotopy {I : Type} {F F' : I -> pType} {f g : forall , F i ->* F' i}
  (h : forall i, f i ==* g i) : fwedge_functor f ==* fwedge_functor g.
  fwedge_pmap_phomotopy (fun i => pwhisker_left (pinl i) (h i))

Definition fwedge_pequiv {I : Type} {F F' : I -> pType} (f : forall i, F i <~>* F' i) : ⋁ F <~>* ⋁ F'.
  let pto . fwedge_functor (fun i => f i) in
  let pfrom . fwedge_functor (fun i => (f i)^-1ᵉ*) in
Proof.
  fapply pequiv_of_pmap, exact pto,
  fapply adjointify, exact pfrom,
  { intro y, refine (fwedge_functor_pcompose (fun i => f i) (fun i => (f i)^-1ᵉ*) y)^-1 @ _,
  refine fwedge_functor_phomotopy (fun i => pright_inv (f i)) y @ _,
  exact fwedge_functor_pid y
  },
  { intro y, refine (fwedge_functor_pcompose (fun i => (f i)^-1ᵉ*) (fun i => f i) y)^-1 @ _,
  refine fwedge_functor_phomotopy (fun i => pleft_inv (f i)) y @ _,
  exact fwedge_functor_pid y
  }
Defined.

Definition plift_fwedge.{u v} {I : Type} (F : I -> pType.{u}) : plift.{u v} (⋁ F) <~>* ⋁ (plift.{u v} o F).
  calc plift.{u v} (⋁ F) <~>* ⋁ F : by exact !pequiv_plift ^-1ᵉ*
  ... <~>* ⋁ (fun i => plift.{u v} (F i)) : by exact fwedge_pequiv (fun i => !pequiv_plift)

Definition fwedge_down_left.{u v} {I : Type} (F : I -> pType) : ⋁ (F o down.{u v}) <~>* ⋁ F.
  proof
  let pto . @fwedge_pmap (lift.{u v} I) (F o down) (⋁ F) (fun i => pinl (down i)) in
  let pfrom . @fwedge_pmap I F (⋁ (F o down.{u v})) (fun i => pinl (up.{u v} i)) in
Proof.
  fapply pequiv_of_pmap,
  { exact pto },
  fapply adjointify,
  { exact pfrom },
  { intro x, exact calc pto (pfrom x) = fwedge_pmap (fun i => (pto o* pfrom) o* pinl i) x : by exact (fwedge_pmap_eta (pto o* pfrom) x)^-1
  ... = fwedge_pmap (fun i => pto o* (pfrom o* pinl i)) x : by exact fwedge_pmap_phomotopy (fun i => passoc pto pfrom (pinl i)) x
  ... = fwedge_pmap (fun i => pto o* pinl (up.{u v} i)) x : by exact fwedge_pmap_phomotopy (fun i => pwhisker_left pto (fwedge_pmap_beta (fun i => pinl (up.{u v} i)) i)) x
  ... = fwedge_pmap pinl x : by exact fwedge_pmap_phomotopy (fun i => fwedge_pmap_beta (fun i => (pinl (down.{u v} i))) (up.{u v} i)) x
  ... = x : by exact fwedge_pmap_pinl x
  },
  { intro x, exact calc pfrom (pto x) = fwedge_pmap (fun i => (pfrom o* pto) o* pinl i) x : by exact (fwedge_pmap_eta (pfrom o* pto) x)^-1
  ... = fwedge_pmap (fun i => pfrom o* (pto o* pinl i)) x : by exact fwedge_pmap_phomotopy (fun i => passoc pfrom pto (pinl i)) x
  ... = fwedge_pmap (fun i => pfrom o* pinl (down.{u v} i)) x : by exact fwedge_pmap_phomotopy (fun i => pwhisker_left pfrom (fwedge_pmap_beta (fun i => pinl (down.{u v} i)) i)) x
  ... = fwedge_pmap pinl x : by exact fwedge_pmap_phomotopy (fun i =>
Proof. induction i with i,
  exact fwedge_pmap_beta (fun i => (pinl (up.{u v} i))) i
Defined.
  ) x
  ... = x : by exact fwedge_pmap_pinl x
  }

Defined.
  qed

Defined. fwedge
