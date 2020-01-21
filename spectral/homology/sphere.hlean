(*
Copyright (c) 2017 Kuen-Bang Hou (Favonia).
Released under Apache 2.0 license as described in the file LICENSE.

Author: Kuen-Bang Hou (Favonia)
*)

import .basic

open eq pointed group algebra circle sphere nat equiv susp
  function sphere homology int lift

namespace homology

section
  parameter (theory : homology_theory)

  open homology_theory

Definition Hsphere : forall (n : ℤ)(m : ℕ), HH theory n (plift (sphere m)) <~>g HH theory (n - m) (plift (sphere 0)).
Proof.
  intros n m, revert n, induction m with m,
  { exact fun n => isomorphism_ap (fun n => HH theory n (plift (sphere 0))) (sub_zero n)^-1 },
  { intro n, exact calc
  HH theory n (plift (susp (sphere m)))
  <~>g HH theory (succ (pred n)) (plift (susp (sphere m)))
  : by exact isomorphism_ap (fun n => HH theory n (plift (susp (sphere m)))) (succ_pred n)^-1
  ... <~>g HH theory (pred n) (plift (sphere m)) : by exact Hplift_susp theory (pred n) (sphere m)
  ... <~>g HH theory (pred n - m) (plift (sphere 0)) : by exact v_0 (pred n)
  ... <~>g HH theory (n - succ m) (plift (sphere 0))
  : by exact isomorphism_ap (fun n => HH theory n (plift (sphere 0))) (sub_sub n 1 m @ ap (fun m => n - m) (add.comm 1 m))
  }
Defined.
Defined.

Defined. homology
