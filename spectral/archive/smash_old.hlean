 (* below are some old tries to compute (A ∧ S¹) directly -/

exit

  (* smash A S¹ = red_susp A -/

  definition red_susp_of_smash_pcircle [unfold 2] (x : smash A S¹*) : red_susp A :=
  begin
    induction x using smash.elim,
    { induction b, exact base, exact equator a },
    { exact base },
    { exact base },
    { reflexivity },
    { exact circle_elim_constant equator_pt b }
  end

  definition smash_pcircle_of_red_susp [unfold 2] (x : red_susp A) : smash A S¹* :=
  begin
    induction x,
    { exact pt },
    { exact gluel' pt a ⬝ ap (smash.mk a) loop ⬝ gluel' a pt },
    { refine !con.right_inv ◾ _ ◾ !con.right_inv,
      exact ap_is_constant gluer loop ⬝ !con.right_inv }
  end

  definition smash_pcircle_of_red_susp_of_smash_pcircle_pt [unfold 3] (a : A) (x : S¹*) :
    smash_pcircle_of_red_susp (red_susp_of_smash_pcircle (smash.mk a x)) = smash.mk a x :=
  begin
    induction x,
    { exact gluel' pt a },
    { exact abstract begin apply eq_pathover,
      refine ap_compose smash_pcircle_of_red_susp _ _ ⬝ph _,
      refine ap02 _ (elim_loop pt (equator a)) ⬝ !elim_equator ⬝ph _,
      -- make everything below this a lemma defined by path induction?
      refine !con_idp⁻¹ ⬝pv _, refine !con.assoc⁻¹ ⬝ph _, apply whisker_bl, apply whisker_lb,
      apply whisker_tl, apply hrfl end end }
  end

  definition concat2o [unfold 10] {A B : Type} {f g h : A → B} {q : f ~ g} {r : g ~ h} {a a' : A}
    {p : a = a'} (s : q a =[p] q a') (t : r a =[p] r a') : q a ⬝ r a =[p] q a' ⬝ r a' :=
  by induction p; exact idpo

  definition apd_con_fn [unfold 10] {A B : Type} {f g h : A → B} {q : f ~ g} {r : g ~ h} {a a' : A}
    (p : a = a') : apd (λa, q a ⬝ r a) p = concat2o (apd q p) (apd r p) :=
  by induction p; reflexivity

  -- definition apd_con_fn_constant [unfold 10] {A B : Type} {f : A → B} {b b' : B} {q : Πa, f a = b}
  --   {r : b = b'} {a a' : A} (p : a = a') :
  --   apd (λa, q a ⬝ r) p = concat2o (apd q p) (pathover_of_eq _ idp) :=
  -- by induction p; reflexivity


  definition smash_pcircle_pequiv_red [constructor] (A : Type*) : smash A S¹* ≃* red_susp A :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact red_susp_of_smash_pcircle },
      { exact smash_pcircle_of_red_susp },
      { exact abstract begin intro x, induction x,
        { reflexivity },
        { apply eq_pathover, apply hdeg_square,
          refine ap_compose red_susp_of_smash_pcircle _ _ ⬝ ap02 _ !elim_equator ⬝ _ ⬝ !ap_id⁻¹,
          refine !ap_con ⬝ (!ap_con ⬝ !elim_gluel' ◾ !ap_compose'⁻¹) ◾ !elim_gluel' ⬝ _,
          esimp, exact !idp_con ⬝ !elim_loop },
        { exact sorry } end end },
      { intro x, induction x,
        { exact smash_pcircle_of_red_susp_of_smash_pcircle_pt a b },
        { exact gluel pt },
        { exact gluer pt },
        { apply eq_pathover_id_right,
          refine ap_compose smash_pcircle_of_red_susp _ _ ⬝ph _,
          unfold [red_susp_of_smash_pcircle],
          refine ap02 _ !elim_gluel ⬝ph _,
          esimp, apply whisker_rt, exact vrfl },
        { apply eq_pathover_id_right,
          refine ap_compose smash_pcircle_of_red_susp _ _ ⬝ph _,
          unfold [red_susp_of_smash_pcircle],
          -- not sure why so many implicit arguments are needed here...
          refine ap02 _ (@smash.elim_gluer A S¹* _ (λa, circle.elim red_susp.base (equator a)) red_susp.base red_susp.base (λa, refl red_susp.base) (circle_elim_constant equator_pt) b) ⬝ph _,
          apply square_of_eq, induction b,
          { exact whisker_right _ !con.right_inv },
          { apply eq_pathover_dep, refine !apd_con_fn ⬝pho _ ⬝hop !apd_con_fn⁻¹,
            refine ap (λx, concat2o x _) !rec_loop ⬝pho _ ⬝hop (ap011 concat2o (apd_compose1 (λa b, ap smash_pcircle_of_red_susp b) (circle_elim_constant equator_pt) loop) !apd_constant')⁻¹,
            exact sorry }

          }}},
    { reflexivity }
  end

  (* smash A S¹ = susp A -/
  open susp


  definition susp_of_smash_pcircle [unfold 2] (x : smash A S¹*) : susp A :=
  begin
    induction x using smash.elim,
    { induction b, exact pt, exact merid a ⬝ (merid pt)⁻¹ },
    { exact pt },
    { exact pt },
    { reflexivity },
    { induction b, reflexivity, apply eq_pathover_constant_right, apply hdeg_square,
      exact !elim_loop ⬝ !con.right_inv }
  end

  definition smash_pcircle_of_susp [unfold 2] (x : susp A) : smash A S¹* :=
  begin
    induction x,
    { exact pt },
    { exact pt },
    { exact gluel' pt a ⬝ (ap (smash.mk a) loop ⬝ gluel' a pt) },
  end

 -- the definitions below compile, but take a long time to do so and have sorry's in them
  definition smash_pcircle_of_susp_of_smash_pcircle_pt [unfold 3] (a : A) (x : S¹*) :
    smash_pcircle_of_susp (susp_of_smash_pcircle (smash.mk a x)) = smash.mk a x :=
  begin
    induction x,
    { exact gluel' pt a },
    { exact abstract begin apply eq_pathover,
      refine ap_compose smash_pcircle_of_susp _ _ ⬝ph _,
      refine ap02 _ (elim_loop north (merid a ⬝ (merid pt)⁻¹)) ⬝ph _,
      refine !ap_con ⬝ (!elim_merid ◾ (!ap_inv ⬝ !elim_merid⁻²)) ⬝ph _,
      -- make everything below this a lemma defined by path induction?
      exact sorry,
      -- refine !con_idp⁻¹ ⬝pv _, apply whisker_tl, refine !con.assoc⁻¹ ⬝ph _,
      -- apply whisker_bl, apply whisker_lb,
      -- refine !con_idp⁻¹ ⬝pv _, apply whisker_tl, apply hrfl
      -- refine !con_idp⁻¹ ⬝pv _, apply whisker_tl,
      -- refine !con.assoc⁻¹ ⬝ph _, apply whisker_bl, apply whisker_lb, apply hrfl
      -- apply square_of_eq, rewrite [+con.assoc], apply whisker_left, apply whisker_left,
      -- symmetry, apply con_eq_of_eq_inv_con, esimp, apply con_eq_of_eq_con_inv,
      -- refine _⁻² ⬝ !con_inv, refine _ ⬝ !con.assoc,
      -- refine _ ⬝ whisker_right _ !inv_con_cancel_right⁻¹, refine _ ⬝ !con.right_inv⁻¹,
      -- refine !con.right_inv ◾ _, refine _ ◾ !con.right_inv,
      -- refine !ap_mk_right ⬝ !con.right_inv
      end end }
  end

  -- definition smash_pcircle_of_susp_of_smash_pcircle_gluer_base (b : S¹*)
  --   : square (smash_pcircle_of_susp_of_smash_pcircle_pt (Point A) b)
  --            (gluer pt)
  --            (ap smash_pcircle_of_susp (ap (λ a, susp_of_smash_pcircle a) (gluer b)))
  --            (gluer b) :=
  -- begin
  --   refine ap02 _ !elim_gluer ⬝ph _,
  --   induction b,
  --   { apply square_of_eq, exact whisker_right _ !con.right_inv },
  --   { apply square_pathover', exact sorry }
  -- end

exit
  definition smash_pcircle_pequiv [constructor] (A : Type*) : smash A S¹* ≃* susp A :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact susp_of_smash_pcircle },
      { exact smash_pcircle_of_susp },
      { exact abstract begin intro x, induction x,
        { reflexivity },
        { exact merid pt },
        { apply eq_pathover_id_right,
          refine ap_compose susp_of_smash_pcircle _ _ ⬝ph _,
          refine ap02 _ !elim_merid ⬝ph _,
          rewrite [↑gluel', +ap_con, +ap_inv, -ap_compose'],
          refine (_ ◾ _⁻² ◾ _ ◾ (_ ◾ _⁻²)) ⬝ph _,
          rotate 5, do 2 (unfold [susp_of_smash_pcircle]; apply elim_gluel),
          esimp, apply elim_loop, do 2 (unfold [susp_of_smash_pcircle]; apply elim_gluel),
          refine idp_con (merid a ⬝ (merid (Point A))⁻¹) ⬝ph _,
          apply square_of_eq, refine !idp_con ⬝ _⁻¹, apply inv_con_cancel_right } end end },
      { intro x, induction x using smash.rec,
        { exact smash_pcircle_of_susp_of_smash_pcircle_pt a b },
        { exact gluel pt },
        { exact gluer pt },
        { apply eq_pathover_id_right,
          refine ap_compose smash_pcircle_of_susp _ _ ⬝ph _,
          unfold [susp_of_smash_pcircle],
          refine ap02 _ !elim_gluel ⬝ph _,
          esimp, apply whisker_rt, exact vrfl },
        { apply eq_pathover_id_right,
          refine ap_compose smash_pcircle_of_susp _ _ ⬝ph _,
          unfold [susp_of_smash_pcircle],
          refine ap02 _ !elim_gluer ⬝ph _,
          induction b,
          { apply square_of_eq, exact whisker_right _ !con.right_inv },
          { exact sorry}
          }}},
    { reflexivity }
  end

end smash
