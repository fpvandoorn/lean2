 (* below are some old tries to compute (A ∧ S¹) directly *)

exit

  (* smash A S¹ = red_susp A *)

Definition red_susp_of_smash_pcircle (x : smash A S¹*) : red_susp A.
Proof.
  induction x using smash.elim,
  { induction b, exact base, exact equator a },
  { exact base },
  { exact base },
  { reflexivity },
  { exact circle_elim_constant equator_pt b }
Defined.

Definition smash_pcircle_of_red_susp (x : red_susp A) : smash A S¹*.
Proof.
  induction x,
  { exact (point _) },
  { exact gluel' (point _) a @ ap (smash.mk a) loop @ gluel' a (point _) },
  { refine (con_pV _) ◾ _ ◾ (con_pV _),
  exact ap_is_constant gluer loop @ (con_pV _) }
Defined.

Definition smash_pcircle_of_red_susp_of_smash_pcircle_pt (a : A) (x : S¹*) :
  smash_pcircle_of_red_susp (red_susp_of_smash_pcircle (smash.mk a x)) = smash.mk a x.
Proof.
  induction x,
  { exact gluel' (point _) a },
  { exact abstract begin apply eq_pathover,
  refine ap_compose smash_pcircle_of_red_susp _ _ @ph _,
  refine ap02 _ (elim_loop (point _) (equator a)) @ !elim_equator @ph _,
  refine (concat_p1 _)^-1 @pv _, refine (concat_pp_p _ _ _)^-1 @ph _, apply whisker_bl, apply whisker_lb,
  apply whisker_tl, apply hrfl end end }
Defined.

Definition concat2o [unfold 10] {A B : Type} {f g h : A -> B} {q : f == g} {r : g == h} {a a' : A}
  {p : a = a'} (s : q a =[p] q a') (t : r a =[p] r a') : q a @ r a =[p] q a' @ r a'.
  by induction p; exact idpo

Definition apd_con_fn [unfold 10] {A B : Type} {f g h : A -> B} {q : f == g} {r : g == h} {a a' : A}
  (p : a = a') : apd (fun a => q a @ r a) p = concat2o (apd q p) (apd r p).
  by induction p; reflexivity



Definition smash_pcircle_pequiv_red (A : pType) : smash A S¹* <~>* red_susp A.
Proof.
  fapply pequiv_of_equiv,
  { fapply equiv.MK,
  { exact red_susp_of_smash_pcircle },
  { exact smash_pcircle_of_red_susp },
  { exact abstract begin intro x, induction x,
  { reflexivity },
  { apply eq_pathover, apply hdeg_square,
  refine ap_compose red_susp_of_smash_pcircle _ _ @ ap02 _ !elim_equator @ _ @ !ap_id^-1,
  refine (ap_pp _ _ _) @ ((ap_pp _ _ _) @ !elim_gluel' ◾ !ap_compose'^-1) ◾ !elim_gluel' @ _,
  esimp, exact (concat_1p _) @ !elim_loop },
  { exact sorry } end end },
  { intro x, induction x,
  { exact smash_pcircle_of_red_susp_of_smash_pcircle_pt a b },
  { exact gluel (point _) },
  { exact gluer (point _) },
  { apply eq_pathover_id_right,
  refine ap_compose smash_pcircle_of_red_susp _ _ @ph _,
  unfold [red_susp_of_smash_pcircle],
  refine ap02 _ !elim_gluel @ph _,
  esimp, apply whisker_rt, exact vrfl },
  { apply eq_pathover_id_right,
  refine ap_compose smash_pcircle_of_red_susp _ _ @ph _,
  unfold [red_susp_of_smash_pcircle],
  refine ap02 _ (@smash.elim_gluer A S¹* _ (fun a => circle.elim red_susp.base (equator a)) red_susp.base red_susp.base (fun a => refl red_susp.base) (circle_elim_constant equator_pt) b) @ph _,
  apply square_of_eq, induction b,
  { exact whisker_right _ (con_pV _) },
  { apply eq_pathover_dep, refine !apd_con_fn @pho _ @hop !apd_con_fn^-1,
  refine ap (fun x => concat2o x _) !rec_loop @pho _ @hop (ap011 concat2o (apd_compose1 (fun a b => ap smash_pcircle_of_red_susp b) (circle_elim_constant equator_pt) loop) !apd_constant')^-1,
  exact sorry }

  }}},
  { reflexivity }
Defined.

  (* smash A S¹ = susp A *)
  open susp


Definition susp_of_smash_pcircle (x : smash A S¹*) : susp A.
Proof.
  induction x using smash.elim,
  { induction b, exact (point _), exact merid a @ (merid (point _))^-1 },
  { exact (point _) },
  { exact (point _) },
  { reflexivity },
  { induction b, reflexivity, apply eq_pathover_constant_right, apply hdeg_square,
  exact !elim_loop @ (con_pV _) }
Defined.

Definition smash_pcircle_of_susp (x : susp A) : smash A S¹*.
Proof.
  induction x,
  { exact (point _) },
  { exact (point _) },
  { exact gluel' (point _) a @ (ap (smash.mk a) loop @ gluel' a (point _)) },
Defined.

Definition smash_pcircle_of_susp_of_smash_pcircle_pt (a : A) (x : S¹*) :
  smash_pcircle_of_susp (susp_of_smash_pcircle (smash.mk a x)) = smash.mk a x.
Proof.
  induction x,
  { exact gluel' (point _) a },
  { exact abstract begin apply eq_pathover,
  refine ap_compose smash_pcircle_of_susp _ _ @ph _,
  refine ap02 _ (elim_loop north (merid a @ (merid (point _))^-1)) @ph _,
  refine (ap_pp _ _ _) @ (!elim_merid ◾ (!ap_inv @ !elim_merid⁻²)) @ph _,
  exact sorry,
Defined. end }
Defined.


exit
Definition smash_pcircle_pequiv (A : pType) : smash A S¹* <~>* susp A.
Proof.
  fapply pequiv_of_equiv,
  { fapply equiv.MK,
  { exact susp_of_smash_pcircle },
  { exact smash_pcircle_of_susp },
  { exact abstract begin intro x, induction x,
  { reflexivity },
  { exact merid (point _) },
  { apply eq_pathover_id_right,
  refine ap_compose susp_of_smash_pcircle _ _ @ph _,
  refine ap02 _ !elim_merid @ph _,
  rewrite [↑gluel', +ap_con, +ap_inv, -ap_compose'],
  refine (_ ◾ _⁻² ◾ _ ◾ (_ ◾ _⁻²)) @ph _,
  rotate 5, do 2 (unfold [susp_of_smash_pcircle]; apply elim_gluel),
  esimp, apply elim_loop, do 2 (unfold [susp_of_smash_pcircle]; apply elim_gluel),
  refine idp_con (merid a @ (merid (Point A))^-1) @ph _,
  apply square_of_eq, refine (concat_1p _) @ _^-1, apply inv_con_cancel_right } end end },
  { intro x, induction x using smash.rec,
  { exact smash_pcircle_of_susp_of_smash_pcircle_pt a b },
  { exact gluel (point _) },
  { exact gluer (point _) },
  { apply eq_pathover_id_right,
  refine ap_compose smash_pcircle_of_susp _ _ @ph _,
  unfold [susp_of_smash_pcircle],
  refine ap02 _ !elim_gluel @ph _,
  esimp, apply whisker_rt, exact vrfl },
  { apply eq_pathover_id_right,
  refine ap_compose smash_pcircle_of_susp _ _ @ph _,
  unfold [susp_of_smash_pcircle],
  refine ap02 _ !elim_gluer @ph _,
  induction b,
  { apply square_of_eq, exact whisker_right _ (con_pV _) },
  { exact sorry}
  }}},
  { reflexivity }
Defined.

Defined. smash
