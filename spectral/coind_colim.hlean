(* author: Floris van Doorn *)

import .colimit.seq_colim

open nat seq_colim eq equiv is_equiv is_trunc function

namespace seq_colim

  variables {A : ℕ -> Type} {f : seq_diagram A}

Definition ι0  : A 0 -> seq_colim f.
  ι f

  variable (f)
Definition ι0' : A 0 -> seq_colim f.
  ι f

Definition glue0 (a : A 0) : shift_down f (ι0 (f a)) = ι f a.
  glue f a

Definition rec_coind_point {P : forall (A : ℕ -> Type) (f : seq_diagram A), seq_colim f -> Type}
  (P0 : forall (A) (f : seq_diagram A) (a : A 0), P f (ι0 a))
  (Ps : forall (A) (f : seq_diagram A) (x : seq_colim (shift_diag f)),
  P (shift_diag f) x -> P f (shift_down f x))
  (Pe : forall (A) (f : seq_diagram A) (a : A 0),
  pathover (P f) (Ps f (ι0 (f a)) !P0) (proof glue f a qed) (P0 f a))
  (n : ℕ) : forall {A : ℕ -> Type} {f : seq_diagram A} (a : A n), P f (ι f a).
Proof.
  induction n with n IH: intro A f a,
  { exact P0 f a },
  { exact Ps f (ι _ a) (IH a) }
Defined.

Definition rec_coind_point_succ {P : forall (A : ℕ -> Type) (f : seq_diagram A), seq_colim f -> Type}
  (P0 : forall (A) (f : seq_diagram A) (a : A 0), P f (ι0 a))
  (Ps : forall (A) (f : seq_diagram A) (x : seq_colim (shift_diag f)),
  P (shift_diag f) x -> P f (shift_down f x))
  (Pe : forall (A) (f : seq_diagram A) (a : A 0),
  pathover (P f) (Ps f (ι0 (f a)) !P0) _ (P0 f a))
  (n : ℕ) {A : ℕ -> Type} {f : seq_diagram A} (a : A (succ n)) :
  rec_coind_point P0 Ps Pe (succ n) a = Ps f (ι _ a) (rec_coind_point P0 Ps Pe n a).
  by reflexivity

Definition rec_coind {P : forall (A : ℕ -> Type) (f : seq_diagram A), seq_colim f -> Type}
  (P0 : forall (A) (f : seq_diagram A) (a : A 0), P f (ι0 a))
  (Ps : forall (A) (f : seq_diagram A) (x : seq_colim (shift_diag f)),
  P (shift_diag f) x -> P f (shift_down f x))
  (Pe : forall (A) (f : seq_diagram A) (a : A 0),
  pathover (P f) (Ps f (ι0 (f a)) !P0) (proof glue f a qed) (P0 f a))
  {A : ℕ -> Type} {f : seq_diagram A} (x : seq_colim f) : P f x.
Proof.
  induction x,
  { exact rec_coind_point P0 Ps Pe n a },
  { revert A f a, induction n with n IH: intro A f a,
  { exact Pe f a },
  { rewrite [rec_coind_point_succ _ _ _ n, rec_coind_point_succ],
  note p . IH _ (shift_diag f) a,
  refine change_path _ (pathover_ap _ _ (apo (Ps f) p)),
  exact !elim_glue
  }},
Defined.

Definition rec_coind_pt2 {P : forall (A : ℕ -> Type) (f : seq_diagram A), seq_colim f -> Type}
  (P0 : forall (A) (f : seq_diagram A) (a : A 0), P f (ι0 a))
  (Ps : forall (A) (f : seq_diagram A) (x : seq_colim (shift_diag f)),
  P (shift_diag f) x -> P f (shift_down f x))
  (Pe : forall (A) (f : seq_diagram A) (a : A 0),
  pathover (P f) (Ps f (ι0 (f a)) !P0) _ (P0 f a))
  {A : ℕ -> Type} {f : seq_diagram A} (x : seq_colim (shift_diag f))
  : rec_coind P0 Ps Pe (shift_down f x) = Ps f x (rec_coind P0 Ps Pe x).
Proof.
  induction x,
  { reflexivity },
  { apply eq_pathover_dep,
  apply hdeg_squareover, esimp,
  refine apd_compose2 (rec_coind P0 Ps Pe) _ _ @ _ @ (apd_compose1 (Ps f) _ _)^-1,
  exact sorry
  --refine ap (fun x => pathover_of_pathover_ap _ _ (x)) _ @ _ ,
  }
Defined.

Definition elim_coind_point {P : forall (A : ℕ -> Type) (f : seq_diagram A), Type}
  (P0 : forall (A) (f : seq_diagram A) (a : A 0), P f)
  (Ps : forall (A) (f : seq_diagram A) (x : seq_colim (shift_diag f)), P (shift_diag f) -> P f)
  (Pe : forall (A) (f : seq_diagram A) (a : A 0), Ps f (ι0 (f a)) (P0 _ (f a)) = P0 f a)
  (n : ℕ) : forall {A : ℕ -> Type} (f : seq_diagram A) (a : A n), P f.
Proof.
  induction n with n IH: intro A f a,
  { exact P0 f a },
  { exact Ps f (ι _ a) (IH _ a) }
Defined.

Definition elim_coind_point_succ {P : forall (A : ℕ -> Type) (f : seq_diagram A), Type}
  (P0 : forall (A) (f : seq_diagram A) (a : A 0), P f)
  (Ps : forall (A) (f : seq_diagram A) (x : seq_colim (shift_diag f)), P (shift_diag f) -> P f)
  (Pe : forall (A) (f : seq_diagram A) (a : A 0), Ps f (ι0 (f a)) (P0 _ (f a)) = P0 f a)
  (n : ℕ) {A : ℕ -> Type} {f : seq_diagram A} (a : A (succ n)) :
  elim_coind_point P0 Ps Pe (succ n) f a =
  Ps f (ι _ a) (elim_coind_point P0 Ps Pe n (shift_diag f) a).
  by reflexivity

Definition elim_coind_path {P : forall (A : ℕ -> Type) (f : seq_diagram A), Type}
  (P0 : forall (A) (f : seq_diagram A) (a : A 0), P f)
  (Ps : forall (A) (f : seq_diagram A) (x : seq_colim (shift_diag f)), P (shift_diag f) -> P f)
  (Pe : forall (A) (f : seq_diagram A) (a : A 0), Ps f (ι0 (f a)) (P0 _ (f a)) = P0 f a)
  (n : ℕ) : forall {A : ℕ -> Type} (f : seq_diagram A) (a : A n),
  elim_coind_point P0 Ps Pe (succ n) f (f a) = elim_coind_point P0 Ps Pe n f a.
Proof.
  induction n with n IH: intro A f a,
  { exact Pe f a },
  { rewrite [elim_coind_point_succ _ _ _ n, elim_coind_point_succ],
  note p . IH (shift_diag f) a,
  refine ap011 (Ps f) !glue p }
Defined.

Definition elim_coind {P : forall (A : ℕ -> Type) (f : seq_diagram A), Type}
  (P0 : forall (A) (f : seq_diagram A) (a : A 0), P f)
  (Ps : forall (A) (f : seq_diagram A) (x : seq_colim (shift_diag f)), P (shift_diag f) -> P f)
  (Pe : forall (A) (f : seq_diagram A) (a : A 0), Ps f (ι0 (f a)) (P0 _ (f a)) = P0 f a)
  {A : ℕ -> Type} {f : seq_diagram A} (x : seq_colim f) : P f.
Proof.
  induction x,
  { exact elim_coind_point P0 Ps Pe n f a },
  { exact elim_coind_path P0 Ps Pe n f a },
Defined.

Definition elim_coind_pt2 {P : forall (A : ℕ -> Type) (f : seq_diagram A), Type}
  (P0 : forall (A) (f : seq_diagram A) (a : A 0), P f)
  (Ps : forall (A) (f : seq_diagram A) (x : seq_colim (shift_diag f)), P (shift_diag f) -> P f)
  (Pe : forall (A) (f : seq_diagram A) (a : A 0), Ps f (ι0 (f a)) (P0 _ (f a)) = P0 f a)
  {A : ℕ -> Type} {f : seq_diagram A} (x : seq_colim (shift_diag f))
  : elim_coind P0 Ps Pe (shift_down f x) = Ps f x (elim_coind P0 Ps Pe x).
Proof.
  induction x,
  { reflexivity },
  { apply eq_pathover, apply hdeg_square,
  refine ap_compose (elim_coind P0 Ps Pe) _ _ @ _ @ (ap_eq_ap011 (Ps f) _ _ _)^-1,
  refine ap02 _ !elim_glue @ !elim_glue @ ap011 (ap011 _) !ap_id^-1 !elim_glue^-1 }
Defined.

Defined. seq_colim
