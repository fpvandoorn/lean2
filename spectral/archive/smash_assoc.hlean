
import ..homotopy.smash homotopy.red_susp

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge is_trunc
  function red_susp unit sigma

exit
namespace smash

  variables {A B C : pType}

  open pushout
Definition prod3_of_sum3 (A B C : pType) : A \* C ⊎ A \* B ⊎ C \* B -> A \* B \* C.
Proof.
  intro v, induction v with ac v,
  exact (ac.1, ((point _), ac.2)),
  induction v with ab cb,
  exact (ab.1, (ab.2, (point _))),
  exact ((point _), (cb.2, cb.1))
Defined.

Definition fin3_of_sum3 (A B C : pType) : A \* C ⊎ A \* B ⊎ C \* B -> A ⊎ B ⊎ C.
  sum_functor (fun ac => ac.1) (sum_functor (fun ab => ab.2) (fun cb => cb.1))

Definition smash3 (A B C : pType) : pType.
  pointed.MK (pushout (prod3_of_sum3 A B C) (fin3_of_sum3 A B C)) (inl ((point _), ((point _), (point _))))

Definition to_image {A B : Type} (f : A -> B) (a : A) : sigma (image f).
  ⟨f a, image.mk a idp⟩

Definition pushout_image_prod3_of_sum3 (A B C : pType) : Type.
  pushout (to_image (prod3_of_sum3 A B C)) (fin3_of_sum3 A B C)






  (* attempt 1, direct proof that A ∧ (B ∧ C) <~> smash3 A B C *)

Definition glue1 (a : A) (b : B) : inl (a, (b, (point _))) = inr (inr (inl b)) :> smash3 A B C.
  pushout.glue (inr (inl (a, b)))

Definition glue2 (b : B) (c : C) : inl ((point _), (b, c)) = inr (inr (inr c)) :> smash3 A B C.
  pushout.glue (inr (inr (c, b)))

Definition glue3 (c : C) (a : A) : inl (a, ((point _), c)) = inr (inl a) :> smash3 A B C.
  pushout.glue (inl (a, c))

Definition smash3_of_prod_smash (a : A) (bc : B ∧ C) : smash3 A B C.
Proof.
  induction bc using smash.elim' with b c b c,
  { exact inl (a, (b, c)) },
  { refine glue1 a b @ (glue1 (point _) b)^-1 @ (glue2 b (point _) @ (glue2 (point _) pt)^-1) @ (glue1 (point _) pt @ (glue1 a (point _))^-1) },
  { refine glue3 c a @ (glue3 (point _) a)^-1 @ (glue1 a (point _) @ (glue1 (point _) pt)^-1) @ (glue1 (point _) pt @ (glue1 a (point _))^-1) },
  { exact abstract whisker_right _ (whisker_left _ (con_pV _) @ (concat_p1 _)) @ (concat_pp_p _ _ _) @
  whisker_left _ !inv_con_cancel_left @ (con_pV _) end },
  { exact abstract whisker_right _ (whisker_right _ (con_pV _) @ (concat_1p _)) @ (concat_pp_p _ _ _) @
  whisker_left _ !inv_con_cancel_left @ (con_pV _) end }
Defined.


Definition smash3_of_smash_smash_gluer (bc : B ∧ C) :
  smash3_of_prod_smash ((point _) : A) bc = (point _).
Proof.
  induction bc with b c b c,
  { exact glue2 b c @ (glue2 (point _) c)^-1 @ (glue3 c (point _) @ (glue3 (point _) pt)^-1) },
  { reflexivity },
  { reflexivity },
  { apply eq_pathover_constant_right, apply square_of_eq, refine (concat_p1 _) @ _ @ !elim_gluel^-1,
  refine whisker_right _ (concat_1p _)^-1 @ (con_pV _)^-1 ◾ idp ◾ ((con_pV _) @ (con_pV _)^-1) },
  { apply eq_pathover_constant_right, apply square_of_eq, refine (concat_p1 _) @ _ @ !elim_gluer^-1,
  refine whisker_right _ (con_pV _) @ (concat_1p _) @ (concat_p1 _)^-1 @ whisker_left _ (con_pV _)^-1 @
  (concat_p1 _)^-1 @ whisker_left _ (con_pV _)^-1 }
Defined.

Definition smash3_of_smash_smash (x : A ∧ (B ∧ C)) : smash3 A B C.
Proof.
  induction x using smash.elim' with a bc a bc,
  { exact smash3_of_prod_smash a bc },
  { exact glue1 a (point _) @ (glue1 (point _) pt)^-1 },
  { exact smash3_of_smash_smash_gluer bc },
  { apply con.right_inv },
  { exact (con_pV _) ◾ (con_pV _) }
Defined.

Definition smash_smash_of_smash3 (x : smash3 A B C) : A ∧ (B ∧ C).
Proof.
  induction x,
  { exact smash.mk a.1 (smash.mk a.2.1 a.2.2) },
  { exact (point _) },
  { exact abstract begin induction x with ac x,
  { induction ac with a c, exact ap (smash.mk a) (gluer' c (point _)) @ gluel' a (point _) },
  induction x with ab cb,
  { induction ab with a b, exact ap (smash.mk a) (gluel' b (point _)) @ gluel' a (point _) },
  { induction cb with c b, exact gluer' (smash.mk b c) (point _) } end end },
Defined.

Definition smash3_of_smash_smash_of_smash3_inl (x : A \* B \* C) :
  smash3_of_smash_smash (smash_smash_of_smash3 (inl x)) = inl x.
Proof.
  induction x with a x, induction x with b c, reflexivity
Defined.

Definition smash3_of_smash_smash_of_smash3_inr (x : A ⊎ B ⊎ C) :
  smash3_of_smash_smash (smash_smash_of_smash3 (inr x)) = inr x.
Proof.
  induction x with a x,
  { exact (glue1 (point _) pt @ (glue1 a (point _))^-1) @ glue3 (point _) a},
  induction x with b c,
  { exact (glue2 (point _) pt @ (glue2 b (point _))^-1) @ glue1 (point _) b},
  { exact (glue3 (point _) pt @ (glue3 c (point _))^-1) @ glue2 (point _) c}
Defined.

  attribute smash_smash_of_smash3_1 [unfold 4]

Definition smash_smash_of_smash3_of_prod_smash (a : A) (bc : B ∧ C) :
  smash_smash_of_smash3 (smash3_of_prod_smash a bc) = smash.mk a bc.
Proof.
  induction bc with b c b c,
  { reflexivity },
  { exact ap (smash.mk a) (gluel (point _)) },
  { exact ap (smash.mk a) (gluer (point _)) },
  { apply eq_pathover, refine ap_compose smash_smash_of_smash3 _ _ @ ap02 _ !elim_gluel @ph _,
  refine (ap_pp _ _ _) @ ((ap_pp _ _ _) @ ((ap_pp _ _ _) @ !pushout.elim_glue ◾ (!ap_inv @ _⁻²)) ◾ ((ap_pp _ _ _) @ !pushout.elim_glue ◾ (!ap_inv @ _⁻²))) ◾ ((ap_pp _ _ _) @ !pushout.elim_glue ◾ (!ap_inv @ _⁻²)) @ph _, rotate 3, do 3 exact !pushout.elim_glue, esimp,
  exact sorry },
  { apply eq_pathover, refine ap_compose smash_smash_of_smash3 _ _ @ ap02 _ !elim_gluer @ph _,
  refine (ap_pp _ _ _) @ ((ap_pp _ _ _) @ ((ap_pp _ _ _) @ !pushout.elim_glue ◾ (!ap_inv @ _⁻²)) ◾ ((ap_pp _ _ _) @ !pushout.elim_glue ◾ (!ap_inv @ _⁻²))) ◾ ((ap_pp _ _ _) @ !pushout.elim_glue ◾ (!ap_inv @ _⁻²)) @ph _, rotate 3, do 3 exact !pushout.elim_glue,
  exact sorry }
Defined.

Definition smash_smash_equiv_smash3 (A B C : pType) : A ∧ (B ∧ C) <~>* smash3 A B C.
Proof.
  fapply pequiv_of_equiv,
  { fapply equiv.MK,
  { exact smash3_of_smash_smash },
  { exact smash_smash_of_smash3 },
  { intro x, --induction x,
  exact sorry
},
  { intro x, induction x with a bc a bc,
  { exact smash_smash_of_smash3_of_prod_smash a bc },
  { apply gluel },
  { apply gluer },
  { apply eq_pathover_id_right, refine ap_compose smash_smash_of_smash3 _ _ @ ap02 _ !elim_gluel @ph _,
  refine (ap_pp _ _ _) @ (!pushout.elim_glue ◾ (!ap_inv @ !pushout.elim_glue⁻²)) @ph _, apply sorry, },
  { apply eq_pathover_id_right, refine ap_compose smash_smash_of_smash3 _ _ @ ap02 _ !elim_gluer @ph _,
  induction bc with b c b c,
  { refine (ap_pp _ _ _) @ ((ap_pp _ _ _) @ !pushout.elim_glue ◾ (!ap_inv @ _⁻²)) ◾ ((ap_pp _ _ _) @ !pushout.elim_glue ◾ (!ap_inv @ _⁻²)) @ph _, rotate 2, do 2 apply !pushout.elim_glue, exact sorry },
  { exact sorry },
  { exact sorry },
  { exact sorry },
  { exact sorry }}}},
  { reflexivity }
Defined.



Defined. smash

  (* attempt 2: proving the induction principle of smash3 A B C for A ∧ (B ∧ C) *)

namespace smash

  variables {A B C : pType}

  (* an induction principle which has only 1 point constructor, but which has bad computation properties *)
  protectedDefinition rec' {P : smash A B -> Type} (Pmk : forall a b, P (smash.mk a b))
  (Pgl : forall a, Pmk a (point _) =[gluel' a (point _)] Pmk (point _) pt)
  (Pgr : forall b, Pmk (point _) b =[gluer' b (point _)] Pmk (point _) pt) (x : smash' A B) : P x.
Proof.
  induction x using smash.rec,
  { apply Pmk },
  { exact gluel (point _) # Pmk (point _) pt },
  { exact gluer (point _) # Pmk (point _) pt },
  { refine change_path _ (Pgl a @o !pathover_tr), apply inv_con_cancel_right },
  { refine change_path _ (Pgr b @o !pathover_tr), apply inv_con_cancel_right }
Defined.



Definition inl3 (a : A) (b : B) (c : C) : A ∧ (B ∧ C).
  smash.mk a (smash.mk b c)

Definition aux1 (a : A) : A ∧ (B ∧ C) . pt
Definition aux2 (b : B) : A ∧ (B ∧ C) . pt
Definition aux3 (c : C) : A ∧ (B ∧ C) . pt

Definition glue12 (a : A) (b : B) : inl3 a b ((point _) : C) = aux1 a.
  ap (smash.mk a) (gluel' b (point _)) @ gluel' a pt

Definition glue23 (b : B) (c : C) : inl3 ((point _) : A) b c = aux2 b.
  gluer' (smash.mk b c) pt

Definition glue31 (c : C) (a : A) : inl3 a ((point _) : B) c = aux3 c.
  ap (smash.mk a) (gluer' c (point _)) @ gluel' a pt

Definition glue1_eq (a : A) : glue12 a (point _) = glue31 (point _) a :> (_ = _ :> (A ∧ (B ∧ C))).
  whisker_right _ (ap02 _ ((con_pV _) @ (con_pV _)^-1))

Definition glue2_eq (b : B) : glue23 b (point _) = glue12 (point _) b :> (_ = _ :> (A ∧ (B ∧ C))).
  (concat_p1 _)^-1 @ !ap_mk_right^-1 ◾ (con_pV _)^-1

Definition glue3_eq (c : C) : glue31 c (point _) = glue23 (point _) c :> (_ = _ :> (A ∧ (B ∧ C))).
  !ap_mk_right ◾ (con_pV _) @ (concat_p1 _)

local attribute ap_mk_right [reducible]

Definition concat3 {A : Type} {x y z : A} {p p' : x = y} {q q' : y = z}
  {r r' : p = p'} {s s' : q = q'} : r = r' -> s = s' -> r ◾ s = r' ◾ s'.
  ap011 concat2

Definition glue_eq2 : glue3_eq ((point _) : A) @ glue2_eq ((point _) : B) @ glue1_eq ((point _) : C) = idp.
Proof.
  unfold [glue1_eq, glue2_eq, glue3_eq],
  refine proof ap011 concat2 proof (ap_is_constant_idp _ _ (con_pV _)) qed idp qed ◾
  ((concat_1p _) @ proof ap011 concat2 proof (ap_is_constant_idp _ _ (con_pV _)) qed⁻² idp qed) ◾
  idp @ _,
  refine whisker_right _ _ @ _,
  exact ((ap02 (smash.mk (Point C)) (con.right_inv (gluer (Point A))) @ (con.right_inv
  (gluer (smash.mk (Point B) (Point A))))^-1) @ (ap02 (smash.mk (Point C))
  (con.right_inv (gluel (Point B))) @ (con.right_inv
  (gluer (smash.mk (Point B) (Point A))))^-1)^-1) ◾ idp,
  { refine _ @ concat3 idp (con.right_inv  (con.right_inv (gluel (Point C)))),
  refine proof idp qed @ !con2_con_con2 },
  refine !con2_con_con2 @ _,
  refine ap (whisker_right _) _ @ whisker_right_idp_left _ _,
  refine idp ◾ !inv_con_inv_right ◾ idp @ _,
  refine whisker_right _ ((concat_pp_p _ _ _) @ whisker_left _ (!inv_con_cancel_left @ !ap_inv^-1)) @ _,
  refine whisker_right _ (ap_pp _ _ _)^-1 @ (ap_pp _ _ _)^-1 @ _,
  refine ap_is_constant (@is_constant.eq _ _ _ (@is_constant_ap _ _ _ _ _ _)) _ @ (con_pV _),
  constructor, exact gluer
Defined.

Definition glue12_cancel (a : A) (b : B) : @glue12 A B C a b @ (glue12 a (point _))^-1 @ ap (smash.mk a) (gluel (point _)) = ap (smash.mk a) (gluel b).
Proof.
  unfold [glue12],
  refine whisker_right _ (whisker_left _ !con_inv @ whisker_left _ (whisker_left _ (ap02 _ (con_pV _))⁻² @ (concat_p1 _)) @ !con_inv_cancel_right) @ _,
  refine (ap_pp _ _ _)^-1 @ ap02 _ !inv_con_cancel_right,
Defined.

Definition glue12_cancel_pt_pt : @glue12_cancel A B C (point _) pt = whisker_right _ (con_pV _) @ (concat_1p _).
  sorry

Definition glue12_over {P : A ∧ (B ∧ C) -> Type} (Ppt : forall a b c, P (inl3 a b c))
  (P1 : forall a, P (aux1 a))
  (P12 : forall a b, Ppt a b (point _) =[glue12 a b] P1 a)
  (a : A) (b : B) : pathover P (Ppt a b (point _)) (ap (smash.mk a) (gluel b)) (transport P (ap (smash.mk a) (gluel (point _))) (Ppt a (point _) pt)).
Proof.
  exact change_path (glue12_cancel a b) (P12 a b @o (P12 a (point _))^-1ᵒ @o pathover_tr (ap (smash.mk a) (gluel (point _))) (Ppt a (point _) pt))
Defined.

Definition glue12_over_pt_pt {P : A ∧ (B ∧ C) -> Type} (Ppt : forall a b c, P (inl3 a b c))
  (P1 : forall a, P (aux1 a))
  (P12 : forall a b, Ppt a b (point _) =[glue12 a b] P1 a) :
  glue12_over Ppt P1 P12 (point _) pt = pathover_tr (ap (smash.mk (point _)) (gluel (point _))) (Ppt (point _) pt (point _)).
  sorry

Definition smash3_rec_mk [unfold 13] {P : A ∧ (B ∧ C) -> Type} (Ppt : forall a b c, P (inl3 a b c))
  (P1 : forall a, P (aux1 a)) (P2 : forall b, P (aux2 b)) (P3 : forall c, P (aux3 c))
  (P12 : forall a b, Ppt a b (point _) =[glue12 a b] P1 a)
  (P23 : forall b c, Ppt (point _) b c =[glue23 b c] P2 b)
  (P31 : forall c a, Ppt a (point _) c =[glue31 c a] P3 c)
  (a : A) (bc : B ∧ C) : P (smash.mk a bc).
Proof.
  induction bc with b c b c,
  { exact Ppt a b c },
  { refine transport P _ (Ppt a (point _) pt), exact ap (smash.mk a) (gluel (point _)) }, --refine transport P _ (Ppt (point _) pt (point _)),
  { refine transport P _ (Ppt a (point _) pt), exact ap (smash.mk a) (gluer (point _)) },
  { exact pathover_of_pathover_ap P (smash.mk a) (glue12_over Ppt P1 P12 a b) },
  { exact sorry }
Defined.

Definition apd_constant' {A : Type} {B : Type} {a a' : A} (p : a = a') {b : B} : apd (fun a => b) p = pathover_of_eq p idp.
  by induction p; reflexivity

Definition change_path_eq_of_eq_change_path' {A : Type} {B : A -> Type} {a a₂ : A} {p p' : a = a₂} {b : B a} {b₂ : B a₂}
  {r : p = p'} {q : b =[p] b₂} {q' : b =[p'] b₂} : change_path r q = q' -> q = change_path r^-1 q'.
Proof.
  induction r, intro s, exact s
Defined.

Definition change_path_eq_of_eq_change_path {A : Type} {B : A -> Type} {a a₂ : A} {p p' : a = a₂} {b : B a} {b₂ : B a₂}
  {r : p = p'} {q : b =[p] b₂} {q' : b =[p'] b₂} : change_path r^-1 q' = q -> q' = change_path r q.
Proof.
  induction r, intro s, exact s
Defined.

Definition pathover_hconcato' {A : Type} {B : A -> Type} {a₀₀ a₂₀ a₀₂ a₂₂ : A}
  (*a₀₀*) {p₁₀ : a₀₀ = a₂₀} (*a₂₀*)
  {p₀₁ : a₀₀ = a₀₂} (*s₁₁*) {p₂₁ : a₂₀ = a₂₂}
  (*a₀₂*) {p₁₂ : a₀₂ = a₂₂} (*a₂₂*)
  {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁}
  {b₀₀ : B a₀₀} {b₂₀ : B a₂₀}
  {b₀₂ : B a₀₂} {b₂₂ : B a₂₂}
  (*b₀₀*) {q₁₀ : b₀₀ =[p₁₀] b₂₀} (*b₂₀*)
  {q₀₁ : b₀₀ =[p₀₁] b₀₂} (*t₁₁*) {q₂₁ : b₂₀ =[p₂₁] b₂₂}
  (*b₀₂*) {q₁₂ : b₀₂ =[p₁₂] b₂₂} (*b₂₂*) {p : a₀₀ = a₀₂} {sp : p = p₀₁} {q : b₀₀ =[p] b₀₂}
  (r : change_path sp q = q₀₁) (t₁₁ : squareover B (sp @ph s₁₁) q₁₀ q₁₂ q q₂₁) :
  squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁.
  by induction sp; induction r; exact t₁₁

Definition pathover_hconcato_right_inv {A : Type} {B : A -> Type} {a₀₀ a₂₀ a₀₂ a₀₄ a₂₂ : A}
  (*a₀₀*) {p₁₀ : a₀₀ = a₂₀} (*a₂₀*)
  {p₀₁ : a₀₀ = a₀₂} {p₀₃ : a₀₂ = a₀₄} (*s₁₁*) {p₂₁ : a₂₀ = a₂₂}
  (*a₀₂*) {p₁₂ : a₀₂ = a₂₂} (*a₂₂*)
  {s₁₁ : square p₁₀ p₁₂ (p₀₁ @ p₀₃ @ p₀₃^-1) p₂₁}
  {b₀₀ : B a₀₀} {b₂₀ : B a₂₀}
  {b₀₂ : B a₀₂} {b₂₂ : B a₂₂} {b₀₄ : B a₀₄}
  (*b₀₀*) {q₁₀ : b₀₀ =[p₁₀] b₂₀} (*b₂₀*)
  {q₀₁ : b₀₀ =[p₀₁] b₀₂} {q₀₃ : b₀₂ =[p₀₃] b₀₄} (*t₁₁*) {q₂₁ : b₂₀ =[p₂₁] b₂₂}
  (*b₀₂*) {q₁₂ : b₀₂ =[p₁₂] b₂₂} (*b₂₂*) --{p : a₀₀ = a₀₂} {sp : p = p₀₁} {q : b₀₀ =[p] b₀₂}
  (t₁₁ : squareover B (!con_inv_cancel_right^-1 @ph s₁₁) q₁₀ q₁₂ q₀₁ q₂₁) :
  squareover B s₁₁ q₁₀ q₁₂ (q₀₁ @o q₀₃ @o q₀₃^-1ᵒ) q₂₁.
Proof.
  exact sorry
Defined.


Definition smash3_rec_23 {P : A ∧ (B ∧ C) -> Type} (Ppt : forall a b c, P (inl3 a b c))
  (P1 : forall a, P (aux1 a)) (P2 : forall b, P (aux2 b)) (P3 : forall c, P (aux3 c))
  (P12 : forall a b, Ppt a b (point _) =[glue12 a b] P1 a)
  (P23 : forall b c, Ppt (point _) b c =[glue23 b c] P2 b)
  (P31 : forall c a, Ppt a (point _) c =[glue31 c a] P3 c) (b : B) (c : C) :
  pathover P (Ppt (point _) b c) (gluer' (smash.mk b c) (smash.mk' (point _) pt)) (Ppt (point _) pt (point _)).
Proof.
  refine change_path _ (P23 b c @o ((P23 b (point _))^-1ᵒ @o P12 (point _) b) @o (P12 (point _) pt)^-1ᵒ),
  refine whisker_left _ (whisker_right _ !glue2_eq⁻² @ (con_Vp _)) ◾ (ap02 _ (con_pV _) ◾ (con_pV _))⁻² @ _,
  reflexivity
Defined.

Definition smash3_rec {P : A ∧ (B ∧ C) -> Type} (Ppt : forall a b c, P (inl3 a b c))
  (P1 : forall a, P (aux1 a)) (P2 : forall b, P (aux2 b)) (P3 : forall c, P (aux3 c))
  (P12 : forall a b, Ppt a b (point _) =[glue12 a b] P1 a)
  (P23 : forall b c, Ppt (point _) b c =[glue23 b c] P2 b)
  (P31 : forall c a, Ppt a (point _) c =[glue31 c a] P3 c)
  (x : A ∧ (B ∧ C)) : P x.
Proof.
  induction x using smash.rec' with a bc a bc,
  { exact smash3_rec_mk Ppt P1 P2 P3 P12 P23 P31 a bc },
  { refine change_path _ (P31 (point _) a @o (P31 (point _) pt)^-1ᵒ),
  refine (whisker_right _ (ap02 _ (con_pV _))) ◾ (ap02 _ (con_pV _) ◾ (con_pV _))⁻² @ _, apply idp_con },
  { induction bc using smash.rec' with b c b c,
  { exact smash3_rec_23 Ppt P1 P2 P3 P12 P23 P31 b c },
  { apply pathover_pathover,
  refine ap (pathover_ap _ _) (!apd_con @ ap011 concato !rec_gluel
  (!apd_inv @ ap inverseo !rec_gluel @ !pathover_of_pathover_ap_invo^-1) @ !pathover_of_pathover_ap_cono^-1) @pho _,
  refine _ @hop (ap (pathover_ap _ _) !apd_constant')^-1,
  refine to_right_inv (pathover_compose P (smash.mk (point _)) _ _ _) _ @pho _,
  apply squareover_change_path_left,
  refine !change_path_cono^-1 @pho _,
  apply squareover_change_path_left,
  refine ap (fun x => _ @o x^-1ᵒ) !glue12_over_pt_pt @pho _,
  apply pathover_hconcato_right_inv,
  exact sorry },
  { exact sorry }}
Defined.

(* 3rd attempt, proving an induction principle without the aux-points induction principle for the smash *)




Defined. smash
