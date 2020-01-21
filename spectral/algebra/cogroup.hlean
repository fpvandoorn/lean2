import algebra.group_theory ..pointed ..homotopy.smash

open eq pointed algebra group eq equiv is_trunc is_conn prod prod.ops
  smash susp unit pushout trunc prod

section
  variables {A B C : pType}

Definition prod.pair_pmap (f : C ->* A) (g : C ->* B)
  : C ->* A \** B.
  Build_pMap (fun c => (f c, g c)) (pair_eq (point_eq f) (point_eq g))

  (* \** is the product in pType *)
Definition pmap_prod_equiv : (C ->* A \** B) <~> (C ->* A) \* (C ->* B).
Proof.
  apply equiv.MK (fun f => (ppr1 o* f, ppr2 o* f))
  (fun w => prod.elim w prod.pair_pmap),
  { intro p, induction p with f g, apply pair_eq,
  { apply path_pforall, fapply Build_pHomotopy,
  { intro x, reflexivity },
  { symmetry, apply trans (prod_eq_pr1 (point_eq f) (point_eq g)),
  apply inverse, apply idp_con } },
  { apply path_pforall, fapply Build_pHomotopy,
  { intro x, reflexivity },
  { symmetry, apply trans (prod_eq_pr2 (point_eq f) (point_eq g)),
  apply inverse, apply idp_con } } },
  { intro f, apply path_pforall, fapply Build_pHomotopy,
  { intro x, apply prod.eta },
  { symmetry, exact prod.pair_eq_eta (point_eq f) } }
Defined.

  (* since ==* is the identity type of pointed maps, *)
  (* the following follows by univalence, but we give a direct proof *)
  (* if we really have to, we could prove the uncurried version *)
  (* is an equivalence, but it's a pain without eta for products *)
Definition pair_phomotopy {f g : C ->* A \** B}
  (h : ppr1 o* f ==* ppr1 o* g) (k : ppr2 o* f ==* ppr2 o* g)
  : f ==* g.
  Build_pHomotopy (fun x => prod_eq (h x) (k x))
Proof.
  apply prod.prod_eq_assemble,
  { esimp, rewrite [prod.eq_pr1_concat,prod_eq_pr1],
  exact point_htpy h },
  { esimp, rewrite [prod.eq_pr2_concat,prod_eq_pr2],
  exact point_htpy k }
Defined.

Defined.

(* should be in wedge *)
Definition or_of_wedge {A B : pType} (w : wedge A B)
  : trunc.or (Σ a, w = inl a) (Σ b, w = inr b).
Proof.
  induction w with a b,
  { exact trunc.tr (sum.inl (sigma.mk a idp)) },
  { exact trunc.tr (sum.inr (sigma.mk b idp)) },
  { apply is_prop.elimo }
Defined.

namespace group (* is this the correct namespace? *)

(* TODO: modify h_space to match *)

(* TODO: move these to appropriate places *)
Definition pdiag (A : pType) : A ->* (A \** A).
Build_pMap (fun a => (a, a)) idp

section prod
  variables (A B : pType)

Definition wpr1 (A B : pType) : (A ∨ B) ->* A.
  Build_pMap (wedge.elim (pid A) (pconst B A) idp) idp

Definition wpr2 (A B : pType) : (A ∨ B) ->* B.
  Build_pMap (wedge.elim (pconst A B) (pid B) idp) idp

Definition ppr1_pprod_of_wedge (A B : pType)
  : ppr1 o* pprod_of_wedge A B ==* wpr1 A B.
Proof.
  fconstructor,
  { intro w, induction w with a b,
  { reflexivity },
  { reflexivity },
  { apply eq_pathover, apply hdeg_square,
  apply trans (ap_compose ppr1 (pprod_of_wedge A B) (pushout.glue star)),
  krewrite pushout.elim_glue, krewrite pushout.elim_glue } },
  { reflexivity }
Defined.

Definition ppr2_pprod_of_wedge (A B : pType)
  : ppr2 o* pprod_of_wedge A B ==* wpr2 A B.
Proof.
  fconstructor,
  { intro w, induction w with a b,
  { reflexivity },
  { reflexivity },
  { apply eq_pathover, apply hdeg_square,
  apply trans (ap_compose ppr2 (pprod_of_wedge A B) (pushout.glue star)),
  krewrite pushout.elim_glue, krewrite pushout.elim_glue } },
  { reflexivity }
Defined.

Defined. prod
structure co_h_space [class] (A : pType).
(comul : A ->* (A ∨ A))
(colaw : pprod_of_wedge A A o* comul ==* pdiag A)

open co_h_space

Definition co_h_space_of_counit_laws {A : pType}
  (c : A ->* (A ∨ A))
  (l : wpr1 A A o* c ==* pid A) (r : wpr2 A A o* c ==* pid A)
  : co_h_space A.
co_h_space.mk c (pair_phomotopy
  (calc
  ppr1 o* pprod_of_wedge A A o* c
  ==* (ppr1 o* pprod_of_wedge A A) o* c
  : (passoc ppr1 (pprod_of_wedge A A) c)^-1*
  ... ==* wpr1 A A o* c
  : pwhisker_right c (ppr1_pprod_of_wedge A A)
  ... ==* pid A : l)
  (calc
  ppr2 o* pprod_of_wedge A A o* c
  ==* (ppr2 o* pprod_of_wedge A A) o* c
  : (passoc ppr2 (pprod_of_wedge A A) c)^-1*
  ... ==* wpr2 A A o* c
  : pwhisker_right c (ppr2_pprod_of_wedge A A)
  ... ==* pid A : r))

section
  variables (A : pType) [H : co_h_space A]
  include H

Definition counit_left : wpr1 A A o* comul A ==* pid A.
  calc
  wpr1 A A o* comul A
  ==* (ppr1 o* (pprod_of_wedge A A)) o* comul A
  : (pwhisker_right (comul A) (ppr1_pprod_of_wedge A A))^-1*
  ... ==* ppr1 o* ((pprod_of_wedge A A) o* comul A)
  : passoc ppr1 (pprod_of_wedge A A) (comul A)
  ... ==* pid A
  : pwhisker_left ppr1 (colaw A)

Definition counit_right : wpr2 A A o* comul A ==* pid A.
  calc
  wpr2 A A o* comul A
  ==* (ppr2 o* (pprod_of_wedge A A)) o* comul A
  : (pwhisker_right (comul A) (ppr2_pprod_of_wedge A A))^-1*
  ... ==* ppr2 o* ((pprod_of_wedge A A) o* comul A)
  : passoc ppr2 (pprod_of_wedge A A) (comul A)
  ... ==* pid A
  : pwhisker_left ppr2 (colaw A)

Definition is_conn_co_h_space : is_conn 0 A.
Proof.
  apply is_contr.mk (trunc.tr (point _)), intro ta,
  induction ta with a,
  have t : trunc -1 ((Σ b, comul A a = inl b) ⊎ (Σ c, comul A a = inr c)),
  from (or_of_wedge (comul A a)),
  induction t with s, induction s with bp cp,
  { induction bp with b p, apply ap trunc.tr,
  exact (ap (wpr2 A A) p)^-1 @ (counit_right A a) },
  { induction cp with c p, apply ap trunc.tr,
  exact (ap (wpr1 A A) p)^-1 @ (counit_left A a) }
Defined.

Defined.

section
  variable (A : pType)

Definition pinch : ⅀ A ->* wedge (⅀ A) (⅀ A).
Proof.
  fapply Build_pMap,
  { intro sa, induction sa with a,
  { exact inl north }, { exact inr south },
  { exact ap inl (glue a @ (glue (point _))^-1) @ glue star @ ap inr (glue a) } },
  { reflexivity }
Defined.

Definition co_h_space_susp : co_h_space (⅀ A).
  co_h_space_of_counit_laws (pinch A)
Proof.
  fapply Build_pHomotopy,
  { intro sa, induction sa with a,
  { reflexivity },
  { exact glue (point _) },
  { apply eq_pathover,
  krewrite [ap_id,-ap_compose' (wpr1 (⅀ A) (⅀ A)) (pinch A)],
  krewrite elim_merid, rewrite ap_con,
  krewrite [pushout.elim_inr,ap_constant],
  rewrite ap_con, krewrite [pushout.elim_inl,pushout.elim_glue,ap_id],
  apply square_of_eq, apply trans (concat_1p _), apply inverse,
  apply trans (con.assoc (merid a) (glue (point _))^-1 (glue (point _))),
  exact whisker_left (merid a) (con.left_inv (glue (point _))) } },
  { reflexivity }
Defined.
Proof.
  fapply Build_pHomotopy,
  { intro sa, induction sa with a,
  { reflexivity },
  { reflexivity },
  { apply eq_pathover,
  krewrite [ap_id,-ap_compose' (wpr2 (⅀ A) (⅀ A)) (pinch A)],
  krewrite elim_merid, rewrite ap_con,
  krewrite [pushout.elim_inr,ap_id],
  rewrite ap_con, krewrite [pushout.elim_inl,pushout.elim_glue,ap_constant],
  apply square_of_eq, apply trans (concat_1p _), apply inverse,
  exact idp_con (merid a) } },
  { reflexivity }
Defined.

Defined.
(*
  terminology: magma, comagma? co_h_space/co_h_space?
  pre_inf_group? pre_inf_cogroup? ghs (for group-like H-space?)
  cgcohs (cogroup-like co-H-space?) cogroup_like_co_h_space?
*)

Defined. group
