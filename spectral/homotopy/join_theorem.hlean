(*- Authors: Clive, Egbert -*)

import homotopy.connectedness homotopy.join

open eq sigma pi function join is_conn is_trunc equiv is_equiv

namespace retraction
  variables {A B C : Type} (r2 : B -> C) (r1 : A -> B)


Definition is_retraction_compose
  [Hr2 : is_retraction r2] [Hr1 : is_retraction r1] :
  is_retraction (r2 o r1).
Proof.
  cases Hr2 with s2 s2_is_right_inverse,
  cases Hr1 with s1 s1_is_right_inverse,
  fapply is_retraction.mk,
  { exact s1 o s2},
  { intro b, esimp,
  calc
  r2 (r1 (s1 (s2 (b)))) = r2 (s2 (b)) : ap r2 (s1_is_right_inverse (s2 b))
  ... = b           : s2_is_right_inverse b

  }, (*- QED -*)
Defined.

Definition is_retraction_compose_equiv_left [Hr2 : is_equiv r2] [Hr1 : is_retraction r1] : is_retraction (r2 o r1).
Proof.
  apply is_retraction_compose,
Defined.

Definition is_retraction_compose_equiv_right [Hr2 : is_retraction r2] [Hr1 :  is_equiv r1] : is_retraction (r2 o r1).
Proof.
  apply is_retraction_compose,
Defined.

Defined. retraction

namespace is_conn
section

  open retraction

  universe variable u
  parameters (n : ℕ₋₂) {A : Type.{u}}
  parameter sec : forall V : trunctype.{u} n,
  is_retraction (const A : V -> (A -> V))

  include sec

  protectedDefinition intro : is_conn n A.
Proof.
  apply is_conn_of_map_to_unit,
  apply is_conn_fun.intro =>
  intro P,
  refine is_retraction_compose_equiv_right (const A) (pi_unit_left P),
Defined.
Defined.
Defined. is_conn

section Join_Theorem

variables (X Y : Type)
  (m n : ℕ₋₂)
  [HXm : is_conn m X]
  [HYn : is_conn n Y]

include HXm HYn

Definition is_conn_join : is_conn (m +2+ n) (join X Y).
Proof.
  apply is_conn.intro,
  intro V,
  apply is_retraction_of_is_equiv,
  apply is_equiv_of_is_contr_fun =>
  intro f,
  refine is_contr_equiv_closed _ _,
  {exact unit},
  symmetry,
  exact sorry
Defined.

Defined. Join_Theorem
