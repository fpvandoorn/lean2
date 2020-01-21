(*
Copyright (c) 2016 Michael Shulman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shulman, Floris van Doorn, Egbert Rijke, Stefano Piceghello, Yuri Sulyma

*)

import homotopy.LES_of_homotopy_groups ..algebra.splice ..algebra.seq_colim ..homotopy.EM ..homotopy.fwedge
       ..pointed_cubes

open eq nat int susp pointed sigma is_equiv equiv fiber algebra trunc trunc_index pi group
     succ_str EM EM.ops function unit lift is_trunc sigma.ops

(*--------------------
  BasicDefinitions
  --------------------*)

(* The basicDefinitions of spectra and prespectra make sense for any successor-structure. *)

structure gen_prespectrum (N : succ_str) :=
  (deloop : N -> pType)
  (glue : forall (n:N), deloop n ->* loops (deloop (S n)))



structure is_spectrum [class] {N : succ_str} (E : gen_prespectrum N) :=
  (is_equiv_glue : forall n, is_equiv (gen_prespectrum.glue E n))



structure gen_spectrum (N : succ_str) :=
  (to_prespectrum : gen_prespectrum N)
  (to_is_spectrum : is_spectrum to_prespectrum)






abbreviation prespectrum := gen_prespectrum +ℤ
Definition prespectrum.mk (Y : ℤ -> pType) (e : forall (n : ℤ), Y n ->* loops (Y (n+1))) : prespectrum :=
gen_prespectrum.mk Y e
abbreviation spectrum := gen_spectrum +ℤ
abbreviation spectrum.mk (Y : prespectrum) (e : is_spectrum Y) : spectrum :=
gen_spectrum.mk Y e

namespace spectrum

Definition glue (N : succ_str}} := @gen_prespectrum.glue N
  --Definition glue := (@gen_prespectrum.glue +ℤ)
Definition equiv_glue {N : succ_str} (E : gen_prespectrum N) [H : is_spectrum E] (n:N) : (E n) <~>* (loops (E (S n))) :=
    pequiv_of_pmap (glue E n) (is_spectrum.is_equiv_glue E n)

Definition equiv_glue2 (Y : spectrum) (n : ℤ) : loops (loops (Y (n+2))) <~>* Y n :=
Proof.
    refine (!equiv_glue @e* loop_pequiv_loop (!equiv_glue @e* loop_pequiv_loop _))^-1ᵉ*,
    refine pequiv_of_eq (ap Y _),
    exact add.assoc n 1 1
Defined.

Definition gluen {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ)
    : X n ->* Ω[k] (X (n +' k)) :=
  by induction k with k f; reflexivity; exact !loopn_succ_in^-1ᵉ* o* Ω->[k] (glue X (n +' k)) o* f

Definition equiv_gluen {N : succ_str} (X : gen_spectrum N) (n : N) (k : ℕ)
    : X n <~>* Ω[k] (X (n +' k)) :=
  by induction k with k f; reflexivity; exact f @e* (loopn_pequiv_loopn k (equiv_glue X (n +' k))
                                                @e* !loopn_succ_in^-1ᵉ*)

Definition equiv_gluen_inv_succ {N : succ_str} (X : gen_spectrum N) (n : N) (k : ℕ) :
    (equiv_gluen X n (k+1))^-1ᵉ* ==*
    (equiv_gluen X n k)^-1ᵉ* o* Ω->[k] (equiv_glue X (n +' k))^-1ᵉ* o* !loopn_succ_in :=
Proof.
    refine !trans_pinv @* pwhisker_left _ _, refine !trans_pinv @* _, refine pwhisker_left _ !pinv_pinv
Defined.

Definition succ_str_add_eq_int_add (n : ℤ) (m : ℕ) : @succ_str.add sint n m = n + m :=
Proof.
    induction m with m IH,
    { symmetry, exact add_zero n },
    { exact ap int.succ IH @ add.assoc n m 1 }
Defined.

Definition glue_ptransport {N : succ_str} (X : gen_prespectrum N) {n n' : N} (p : n = n') :
    glue X n' o* ptransport X p ==* Ω-> (ptransport X (ap S p)) o* glue X n :=
  by induction p; exact !pcompose_pid @* !pid_pcompose^-1* @* pwhisker_right _ !ap1_pid^-1*


Definition psp_of_nat_indexed (E : gen_prespectrum +ℕ) : gen_prespectrum +ℤ :=
    gen_prespectrum.mk
    (fun (n:ℤ) => match n with
             | of_nat k          := E k
             | neg_succ_of_nat k := Ω[succ k] (E 0)
             end)
    begin
      intros n, cases n with n n: esimp,
      { exact (gen_prespectrum.glue E n) },
      cases n with n,
      { exact (pid _) },
      { exact (pid _) }
    end

Definition is_spectrum_of_nat_indexed [instance] (E : gen_prespectrum +ℕ) [H : is_spectrum E] : is_spectrum (psp_of_nat_indexed E) :=
Proof.
    apply is_spectrum.mk, intros n, cases n with n n: esimp,
    { apply is_spectrum.is_equiv_glue },
    cases n with n: apply is_equiv_id
Defined.

  protectedDefinition of_nat_indexed (E : gen_prespectrum +ℕ) [H : is_spectrum E] : spectrum
  := spectrum.mk (psp_of_nat_indexed E) (is_spectrum_of_nat_indexed E)


Definition succ_str.of_nat {N : succ_str} (z : N) : ℕ -> N
  | succ_str.of_nat zero   := z
  | succ_str.of_nat (succ k) := S (succ_str.of_nat k)

Definition psp_of_gen_indexed {N : succ_str} (z : N) (E : gen_prespectrum N) : prespectrum :=
    psp_of_nat_indexed (gen_prespectrum.mk (fun n => E (succ_str.of_nat z n)) (fun n => gen_prespectrum.glue E (succ_str.of_nat z n)))

Definition is_spectrum_of_gen_indexed [instance] {N : succ_str} (z : N) (E : gen_prespectrum N) [H : is_spectrum E]
  : is_spectrum (psp_of_gen_indexed z E) :=
Proof.
    apply is_spectrum_of_nat_indexed, apply is_spectrum.mk, intros n, esimp, apply is_spectrum.is_equiv_glue
Defined.

  protectedDefinition of_gen_indexed {N : succ_str} (z : N) (E : gen_spectrum N) : spectrum :=
    gen_spectrum.mk (psp_of_gen_indexed z E) (is_spectrum_of_gen_indexed z E)

      protectedDefinition MK {N : succ_str} (deloop : N -> pType)
    (glue : forall (n:N), (deloop n) <~>* (loops (deloop (S n)))) : gen_spectrum N :=
    gen_spectrum.mk (gen_prespectrum.mk deloop (fun (n:N) => glue n))
    (begin
      apply is_spectrum.mk, intros n, esimp,
      apply pequiv.to_is_equiv      end)

    protectedDefinition Mk (deloop : ℕ -> pType)
    (glue : forall (n:ℕ), (deloop n) <~>* (loops (deloop (nat.succ n)))) : spectrum :=
    spectrum.of_nat_indexed (spectrum.MK deloop glue)

  ------------------------------
    ------------------------------


  structure smap {N : succ_str} (E F : gen_prespectrum N) :=
    (to_fun : forall , E n ->* F n)
    (glue_square : forall (n:N), psquare
      (to_fun n)
      (Ω-> (to_fun (S n)))
      (glue E n)
      (glue F n)
    )

Definition smap_sigma {N : succ_str} (X Y : gen_prespectrum N) : Type :=
    Σ (to_fun : forall , X n ->* Y n),
    forall (n:N), psquare
      (to_fun n)
      (Ω-> (to_fun (S n)))
      (glue X n)
      (glue Y n)

  open smap
  infix ` ->ₛ `:30 := smap

  attribute smap.to_fun [coercion]

Definition smap_to_sigma {N : succ_str} {X Y : gen_prespectrum N} (f : X ->ₛ Y) : smap_sigma X Y :=
Proof.
    exact sigma.mk (smap.to_fun f) (glue_square f) =>
Defined.

Definition smap_to_struc {N : succ_str} {X Y : gen_prespectrum N} (f : smap_sigma X Y) : X ->ₛ Y :=
Proof.
    exact smap.mk f.1 f.2,
Defined.

Definition smap_to_sigma_isretr {N : succ_str} {X Y : gen_prespectrum N} (f : smap_sigma X Y) :
    smap_to_sigma (smap_to_struc f) = f :=
Proof.
    induction f, reflexivity
Defined.

Definition smap_to_sigma_issec {N : succ_str} {X Y : gen_prespectrum N} (f : X ->ₛ Y) :
    smap_to_struc (smap_to_sigma f) = f :=
Proof.
    induction f, reflexivity
Defined.

Definition smap_sigma_equiv {N : succ_str} (X Y : gen_prespectrum N) : (smap_sigma X Y) <~> (X ->ₛ Y) :=
Proof.
    fapply equiv.mk,
    exact smap_to_struc,
    fapply adjointify,
    exact smap_to_sigma,
    exact smap_to_sigma_issec,
    exact smap_to_sigma_isretr
Defined.

Definition sglue_square {N : succ_str} {E F : gen_spectrum N} (f : E ->ₛ F) (n : N)
    : psquare (f n) (Ω-> (f (S n))) (equiv_glue E n) (equiv_glue F n) :=
  glue_square f n

Definition sid [refl] {N : succ_str} (E : gen_prespectrum N) : E ->ₛ E :=
Proof.
    apply smap.mk (fun n => pid (E n)),
    intro n, exact phrfl @vp* !ap1_pid
Defined.

Definition scompose [trans] {N : succ_str} {X Y Z : gen_prespectrum N}
    (g : Y ->ₛ Z) (f : X ->ₛ Y) : X ->ₛ Z :=
Proof.
    apply smap.mk (fun n => g n o* f n),
    intro n, exact (glue_square f n @h* glue_square g n) @vp* !ap1_pcompose
Defined.

  infixr ` oₛ `:60 := scompose

Definition szero {N : succ_str} (E F : gen_prespectrum N) : E ->ₛ F :=
Proof.
    apply smap.mk (fun n => pconst (E n) (F n)),
    intro n, exact !phconst_square @vp* !ap1_pconst
Defined.

Definition stransport {N : succ_str} {A : Type} {a a' : A} (p : a = a')
  (E : A -> gen_prespectrum N) : E a ->ₛ E a' :=
  smap.mk (fun n => ptransport (fun a => E a n) p)
          begin
            intro n, induction p,
            exact !pcompose_pid @* !pid_pcompose^-1* @* pwhisker_right _ !ap1_pid^-1*,
          end

  structure shomotopy {N : succ_str} {E F : gen_prespectrum N} (f g : E ->ₛ F) :=
    (to_phomotopy : forall n, f n ==* g n)
    (glue_homotopy : forall n, ptube_v
                           (to_phomotopy n)
                           (Ω⇒ (to_phomotopy (S n)))
                           (glue_square f n)
                           (glue_square g n))

(*    (glue_homotopy : forall n, phsquare
                         (pwhisker_left (glue F n) (to_phomotopy n))
                         (pwhisker_right (glue E n) (ap1_phomotopy (to_phomotopy (S n))))
                         (glue_square f n)
                         (glue_square g n))
*)

  infix ` ~ₛ `:50 := shomotopy
  attribute [coercion] shomotopy.to_phomotopy

Definition shomotopy_compose {N : succ_str} {E F : gen_prespectrum N} {f g h : E ->ₛ F} (p : g ~ₛ h) (q : f ~ₛ g) : f ~ₛ h :=
  shomotopy.mk
    (fun n => (shomotopy.to_phomotopy q n) @* (shomotopy.to_phomotopy p n))
    begin
      intro n, unfold [ptube_v],
      rewrite (pwhisker_left_trans _),
      rewrite ap1_phomotopy_trans,
      rewrite (pwhisker_right_trans _),
      exact phhconcat ((shomotopy.glue_homotopy q) n) ((shomotopy.glue_homotopy p) n)
    end

Definition shomotopy_inverse {N : succ_str} {E F : gen_prespectrum N} {f g : E ->ₛ F} (p : f ~ₛ g) : g ~ₛ f :=
  shomotopy.mk (fun n => (shomotopy.to_phomotopy p n)^-1*) begin
    intro n, unfold [ptube_v],
    rewrite (pwhisker_left_symm _ _),
    rewrite [-ap1_phomotopy_symm],
    rewrite (pwhisker_right_symm _ _),
    exact phhinverse ((shomotopy.glue_homotopy p) n)
Defined.


  (* Comparing the structure of shomotopy with a Σ-type *)
Definition shomotopy_sigma {N : succ_str} {X Y : gen_prespectrum N} (f g : X ->ₛ Y) : Type :=
  Σ (phtpy : forall (n : N), f n ==* g n),
    forall n, ptube_v
      (phtpy n)
      (ap1_phomotopy (phtpy (S n)))
      (glue_square f n)
      (glue_square g n)

Definition shomotopy_to_sigma {N : succ_str} {X Y : gen_prespectrum N} {f g : X ->ₛ Y} (H : f ~ₛ g) : shomotopy_sigma f g :=
  ⟨H, shomotopy.glue_homotopy H⟩

Definition shomotopy_to_struct {N : succ_str} {X Y : gen_prespectrum N} {f g : X ->ₛ Y} (H : shomotopy_sigma f g) : f ~ₛ g :=
Proof.
    induction H with H Hsq,
    exact shomotopy.mk H Hsq,
Defined.

Definition shomotopy_to_sigma_isretr {N : succ_str} {X Y : gen_prespectrum N} {f g : X ->ₛ Y} (H : shomotopy_sigma f g) :
    shomotopy_to_sigma (shomotopy_to_struct H) = H
  :=
Proof.
    induction H with H Hsq, reflexivity
Defined.

Definition shomotopy_to_sigma_issec {N : succ_str} {X Y : gen_prespectrum N} {f g : X ->ₛ Y} (H : f ~ₛ g) :
    shomotopy_to_struct (shomotopy_to_sigma H) = H
  :=
Proof.
    induction H, reflexivity
Defined.

Definition shomotopy_sigma_equiv {N : succ_str} {X Y : gen_prespectrum N} (f g : X ->ₛ Y) :
    shomotopy_sigma f g <~> (f ~ₛ g) :=
Proof.
    fapply equiv.mk,
    exact shomotopy_to_struct,
    fapply adjointify,
    exact shomotopy_to_sigma,
    exact shomotopy_to_sigma_issec,
    exact shomotopy_to_sigma_isretr,
Defined.

  (* equivalence of shomotopy and eq *)
  (*
Definition eq_of_shomotopy_pfun {N : succ_str} {X Y : gen_prespectrum N} {f g : X ->ₛ Y} (H : f ~ₛ g) (n : N) : f n = g n :=
Proof.
    fapply inj (smap_sigma_equiv X Y),
    repeat exact sorry
Defined.*)

Definition fam_phomotopy_path
    {N : Type} {X Y: N -> pType} (f g : forall n, X n ->* Y n) : (f = g) <~> (forall n, f n ==* g n) :=
    !eq_equiv_homotopy @e pi_equiv_pi_right (fun n => pmap_eq_equiv (f n) (g n))

(*
Definition phomotopy_rec_on_eq [recursor]
    {k' : ppi B x₀}
    {Q : (k ==* k') -> Type}
    (p : k ==* k')
    (H : forall (q : k = k'), Q (phomotopy_path q))
    : Q p :=
  phomotopy_path_of_phomotopy p # H (path_pforall p)
*)
Definition fam_phomotopy_rec_on_eq {N : Type} {X Y : N -> pType} (f g : forall n, X n ->* Y n)
    {Q : (forall n, f n ==* g n) -> Type}
    (p : forall n, f n ==* g n)
    (H : forall (q : f = g), Q (fam_phomotopy_path f g q)) : Q p :=
Proof.
    refine _ # H ((fam_phomotopy_path f g)^-1ᵉ p),
    have q : to_fun (fam_phomotopy_path f g) (to_fun (fam_phomotopy_path f g)^-1ᵉ p) = p =>
    from right_inv (fam_phomotopy_path f g) p,
    krewrite q
Defined.

(*
Definition phomotopy_rec_idp [recursor]
    {Q : forall {k' : ppi B x₀},  (k ==* k') -> Type}
    (q : Q (reflexivity k)) {k' : ppi B x₀} (H : k ==* k') : Q H :=
Proof.
    induction H using phomotopy_rec_on_eq with t,
    induction t, exact eq_phomotopy_refl_phomotopy_path_refl k # q,
Defined.
*)

--set_option pp.coercions true

Definition fam_phomotopy_rec_idp {N : Type} {X Y : N -> pType} (f : forall n, X n ->* Y n)
    (Q : forall (g : forall n, X n ->* Y n) (H : forall n, f n ==* g n), Type)
    (q : Q f (fun n => (reflexivity _)))
    (g : forall n, X n ->* Y n) (H : forall n, f n ==* g n) : Q g H :=
Proof.
    fapply fam_phomotopy_rec_on_eq,
    refine fun (p : f = g) => _, --ugly trick
    intro p, induction p,
    exact q,
Defined.

Definition eq_of_shomotopy {N : succ_str} {X Y : gen_prespectrum N} {f g : X ->ₛ Y} (H : f ~ₛ g) : f = g :=
Proof.
    fapply inj (smap_sigma_equiv X Y)^-1ᵉ,
    induction f with f fsq,
    induction g with g gsq,
    induction H with H Hsq,
    fapply sigma_eq,
    fapply eq_of_homotopy,
    intro n, fapply path_pforall, exact H n,
    fapply pi_pathover_constant,
    intro n,
    esimp at *,
    revert g H gsq Hsq n,
    refine fam_phomotopy_rec_idp f _ _,
    intro gsq Hsq n,
    refine change_path _ _,
    reflexivity,
    refine (eq_of_homotopy_apd10 rfl)^-1 @ _,
    fapply ap (eq_of_homotopy), fapply eq_of_homotopy, intro n, refine (path_pforall_refl _)^-1,
    fapply pathover_idp_of_eq,
    note Hsq' := ptube_v_eq_bot (reflexivity _) (ap1_phomotopy_refl _) (fsq n) (gsq n) (Hsq n),
    unfold ptube_v at *,
    unfold phsquare at *,
    refine _ @ Hsq'^-1 @ _,
    refine (trans_refl (fsq n))^-1 @ _,
    exact idp ◾** (pwhisker_right_refl _ _)^-1,
    refine _ @ (refl_trans (gsq n)),
    refine _ ◾** idp,
    exact pwhisker_left_refl _ _,
Defined.

  ------------------------------
    ------------------------------

Definition spectrum_pequiv_of_pequiv_succ {E F : spectrum} (n : ℤ) (e : E (n + 1) <~>* F (n + 1)) :
    E n <~>* F n :=
  equiv_glue E n @e* loop_pequiv_loop e @e* (equiv_glue F n)^-1ᵉ*

Definition spectrum_pequiv_of_nat {E F : spectrum} (e : forall (n : ℕ), E n <~>* F n) (n : ℤ) :
    E n <~>* F n :=
Proof.
    induction n with n n,
      exact e n,
    induction n with n IH,
    { exact spectrum_pequiv_of_pequiv_succ -[1+0] (e 0) },
    { exact spectrum_pequiv_of_pequiv_succ -[1+succ n] IH }
Defined.

Definition spectrum_pequiv_of_nat_add {E F : spectrum} (m : ℕ)
    (e : forall (n : ℕ), E (n + m) <~>* F (n + m)) : forall (n : ℤ), E n <~>* F n :=
Proof.
    apply spectrum_pequiv_of_nat,
    refine nat.rec_down _ m e _,
    intro n f k, cases k with k,
    exact spectrum_pequiv_of_pequiv_succ _ (f 0),
    exact pequiv_ap E (ap of_nat (succ_add k n)) @e* f k @e*
          pequiv_ap F (ap of_nat (succ_add k n))^-1
Defined.

Definition is_contr_spectrum_of_nat {E : spectrum} (e : forall (n : ℕ), is_contr (E n)) (n : ℤ) :
    is_contr (E n)  :=
Proof.
    have forall n, is_contr (E (n + 1)) -> is_contr (E n),
    from fun n H => @(is_trunc_equiv_closed_rev -2 !equiv_glue) (is_contr_loop_of_is_contr H),
    induction n with n n,
      exact e n,
    induction n with n IH,
    { exact this -[1+0] (e 0) },
    { exact this -[1+succ n] IH }
Defined.

  structure is_sequiv {N : succ_str} {E F : gen_prespectrum N} (f : E ->ₛ F) : Type :=
  (to_linv : F ->ₛ E)
  (is_retr : to_linv oₛf ~ₛ sid E)
  (to_rinv : F ->ₛ E)
  (is_sec  : f oₛ to_rinv ~ₛ sid F)

  structure sequiv {N : succ_str} (E F : gen_prespectrum N) : Type :=
  (to_fun  : E ->ₛ F)
  (to_is_sequiv : is_sequiv to_fun)

  infix ` <~>ₛ ` : 25 := sequiv

Definition is_sequiv_smap {N : succ_str} {E F : gen_prespectrum N} (f : E ->ₛ F) : Type := forall (n: N), is_equiv (f n)

Definition is_sequiv_of_smap_pequiv {N : succ_str} {E F : gen_prespectrum N} (f : E ->ₛ F) (H : is_sequiv_smap f) (n : N) : E n <~>* F n :=
Proof.
    fapply pequiv_of_pmap,
    exact f n,
    fapply H,
Defined.

Definition is_sequiv_of_smap_inv {N : succ_str} {E F : gen_prespectrum N} (f : E ->ₛ F) (H : is_sequiv_smap f) : F ->ₛ E :=
Proof.
    fapply smap.mk,
    intro n,
    exact (is_sequiv_of_smap_pequiv f H n)^-1ᵉ*,
    intro n,
    refine _ @vp* (to_pinv_loopn_pequiv_loopn 1 (is_sequiv_of_smap_pequiv f H (S n)))^-1*,
    fapply phinverse,
    exact glue_square f n,
Defined.

  local postfix `^-1ˢ` : (max + 1) := is_sequiv_of_smap_inv

Definition is_sequiv_of_smap_isretr {N : succ_str} {E F : gen_prespectrum N} (f : E ->ₛ F) (H : is_sequiv_smap f) : is_sequiv_of_smap_inv f H oₛ f ~ₛ sid E :=
Proof.
    fapply shomotopy.mk,
    intro n,
    fapply pleft_inv,
    intro n,
    refine _ @hp** _,
    repeat exact sorry,
Defined.

Definition is_sequiv_of_smap_issec {N : succ_str} {E F : gen_prespectrum N} (f : E ->ₛ F) (H : is_sequiv_smap f) : f oₛ is_sequiv_of_smap_inv f H ~ₛ sid F :=
Proof.
    repeat exact sorry
Defined.

Definition is_sequiv_of_smap {N : succ_str} {E F : gen_prespectrum N} (f : E ->ₛ F) : is_sequiv_smap f -> is_sequiv f :=
Proof.
    intro H,
    fapply is_sequiv.mk,
    fapply is_sequiv_of_smap_inv f H,
    fapply is_sequiv_of_smap_isretr f H,
    fapply is_sequiv_of_smap_inv f H,
    fapply is_sequiv_of_smap_issec f H,
Defined.

  (*--------
    Fibers
  ---------*)

Definition sfiber {N : succ_str} {X Y : gen_spectrum N} (f : X ->ₛ Y) :
    gen_spectrum N :=
    spectrum.MK (fun n => pfiber (f n))
       (fun n => (loop_pfiber (f (S n)))^-1ᵉ* o*ᵉ pfiber_pequiv_of_square _ _ (sglue_square f n))

  (* the map from the fiber to the domain *)
Definition spoint {N : succ_str} {X Y : gen_spectrum N} (f : X ->ₛ Y) : sfiber f ->ₛ X :=
  smap.mk (fun n => ppoint (f n))
    begin
      intro n,
      refine _ @* !passoc,
      refine _ @* pwhisker_right _ !ppoint_loop_pfiber_inv^-1*,
      rexact (pfiber_pequiv_of_square_ppoint (equiv_glue X n) (equiv_glue Y n) (sglue_square f n))^-1*
    end

Definition scompose_spoint {N : succ_str} {X Y : gen_spectrum N} (f : X ->ₛ Y)
    : f oₛ spoint f ~ₛ !szero :=
Proof.
    fapply shomotopy.mk,
    { intro n, exact pcompose_ppoint (f n) },
    { intro n, esimp, exact sorry }
Defined.

  (*--------------------
    Homotopy groups
   --------------------*)

Definition shomotopy_group (n : ℤ) (E : spectrum) : AbGroup := forall ag[2] (E (2 - n))

  notation `forall ₛ[`:95 n:0 `]`:0 := shomotopy_group n

Definition shomotopy_group_fun (n : ℤ) {E F : spectrum} (f : E ->ₛ F) :
    forall ₛ[n] E ->g forall ₛ[n] F :=
  proof forall ->g[2] (f (2 - n)) qed

Definition shomotopy_group_isomorphism_of_pequiv (n : ℤ) {E F : spectrum} (f : forall n, E n <~>* F n) :
    forall ₛ[n] E <~>g forall ₛ[n] F :=
  by rexact homotopy_group_isomorphism_of_pequiv 1 (f (2 - n))

Definition shomotopy_group_isomorphism_of_pequiv_nat (n : ℕ) {E F : spectrum}
    (f : forall n, E n <~>* F n) : forall ₛ[n] E <~>g forall ₛ[n] F :=
  shomotopy_group_isomorphism_of_pequiv n (spectrum_pequiv_of_nat f)

  notation `forall ₛ->[`:95 n:0 `]`:0 := shomotopy_group_fun n

  (* properties about homotopy groups *)
Definition equiv_glue_neg (X : spectrum) (n : ℤ) : X (2 - succ n) <~>* loops (X (2 - n)) :=
  have H : succ (2 - succ n) = 2 - n, from ap succ !sub_sub^-1 @ sub_add_cancel (2-n) 1,
  equiv_glue X (2 - succ n) @e* loop_pequiv_loop (pequiv_of_eq (ap X H))

Definition forall _glue (X : spectrum) (n : ℤ) : forall [2] (X (2 - succ n)) <~>* forall [3] (X (2 - n)) :=
  homotopy_group_pequiv 2 (equiv_glue_neg X n)

Definition forall g_glue (X : spectrum) (n : ℤ) : forall g[2] (X (2 - succ n)) <~>g forall g[3] (X (2 - n)) :=
Proof.
    change forall g[2] (X (2 - succ n)) <~>g forall g[2] (loops (X (2 - n))),
    apply homotopy_group_isomorphism_of_pequiv,
    exact equiv_glue_neg X n
Defined.

Definition forall g_glue_homotopy_forall _glue (X : spectrum) (n : ℤ) : forall g_glue X n == forall _glue X n :=
  by reflexivity

Definition forall _glue_natural {X Y : spectrum} (f : X ->ₛ Y) (n : ℤ) :
    forall _glue Y n o* forall ->[2] (f (2 - succ n)) ==* forall ->[3] (f (2 - n)) o* forall _glue X n :=
Proof.
    change forall ->[2] (equiv_glue_neg Y n) o* forall ->[2] (f (2 - succ n)) ==*
           forall ->[2] (Ω-> (f (2 - n))) o* forall ->[2] (equiv_glue_neg X n),
    refine homotopy_group_functor_psquare 2 _ =>
    refine !sglue_square @v* ap1_psquare !pequiv_of_eq_natural^-1*
Defined.

Definition homotopy_group_spectrum_irrel_one {n m : ℤ} {k : ℕ} (E : spectrum) (p : n + 1 = m + k)
    [Hk : is_succ k] : forall g[k] (E n) <~>g forall ₁ (E m) :=
Proof.
    induction Hk with k,
    change forall ₁ (Ω[k] (E n)) <~>g forall ₁ (E m),
    apply homotopy_group_isomorphism_of_pequiv 0,
    symmetry,
    have m + k = n, from (pred_succ (m + k))^-1 @ ap pred (add.assoc m k 1 @ p^-1) @ pred_succ n,
    induction (succ_str_add_eq_int_add m k @ this),
    exact equiv_gluen E m k
Defined.

Definition homotopy_group_spectrum_irrel {n m : ℤ} {l k : ℕ} (E : spectrum) (p : n + l = m + k)
    [Hk : is_succ k] [Hl : is_succ l] : forall g[k] (E n) <~>g forall g[l] (E m) :=
  proof
  have forall a b c : ℤ, a + (b + c) = c + (b + a), from fun a b c =>
  !add.assoc^-1 @ add.comm (a + b) c @ ap (fun x => c + x) (add.comm a b),
  have n + 1 = m + 1 - l + k, from
  ap succ (add_sub_cancel n l)^-1 @ !add.assoc @ ap (fun x => x + (-l + 1)) p @ !add.assoc @
  ap (fun x => m + x) (this k (-l) 1) @ !add.assoc^-1 @ !add.assoc^-1,
  homotopy_group_spectrum_irrel_one E this @g
  (homotopy_group_spectrum_irrel_one E (sub_add_cancel (m+1) l)^-1)^-1ᵍ
  qed

Definition shomotopy_group_isomorphism_homotopy_group {n m : ℤ} {l : ℕ} (E : spectrum) (p : n + m = l)
    [H : is_succ l] : forall ₛ[n] E <~>g forall g[l] (E m) :=
  have 2 - n + l = m + 2, from
  ap (fun x => 2 - n + x) p^-1 @ !add.assoc^-1 @ ap (fun x => x + m) (sub_add_cancel 2 n) @ add.comm 2 m,
  homotopy_group_spectrum_irrel E this

Definition shomotopy_group_pequiv_homotopy_group_ab {n m : ℤ} {l : ℕ} (E : spectrum) (p : n + m = l)
    [H : is_at_least_two l] : forall ₛ[n] E <~>g forall ag[l] (E m) :=
Proof.
    induction H with l,
    exact shomotopy_group_isomorphism_homotopy_group E p
Defined.

Definition shomotopy_group_pequiv_homotopy_group {n m : ℤ} {l : ℕ} (E : spectrum) (p : n + m = l) :
    forall ₛ[n] E <~>* forall [l] (E m) :=
Proof.
    cases l with l,
    { apply ptrunc_pequiv_ptrunc, symmetry,
      change E m <~>* loops (loops (E (2 - n))),
      refine !equiv_glue @e* loop_pequiv_loop _,
      refine !equiv_glue @e* loop_pequiv_loop _,
      apply pequiv_ap E,
      have -n = m, from neg_eq_of_add_eq_zero p,
      induction this,
      rexact add.assoc (-n) 1 1 @ add.comm (-n) 2 },
    { exact pequiv_of_isomorphism (shomotopy_group_isomorphism_homotopy_group E p) }
Defined.

  (* the long exact sequence of homotopy groups for spectra *)
  section LES
  open chain_complex prod fin group

  universe variable u
  parameters {X Y : spectrum.{u}} (f : X ->ₛ Y)

Definition LES_of_shomotopy_groups : chain_complex +3ℤ :=
  splice (fun (n : ℤ) => LES_of_homotopy_groups (f (2 - n))) (2, 0)
         (forall _glue Y) (forall _glue X) (forall _glue_natural f)

    example (n : ℤ) : LES_of_shomotopy_groups (n, 0) = forall ₛ[n] Y := idp
  example (n : ℤ) : LES_of_shomotopy_groups (n, 1) = forall ₛ[n] X := idp
  example (n : ℤ) : LES_of_shomotopy_groups (n, 2) = forall ₛ[n] (sfiber f) := idp
  example (n : ℤ) : cc_to_fn LES_of_shomotopy_groups (n, 0) = forall ₛ->[n] f := idp
  example (n : ℤ) : cc_to_fn LES_of_shomotopy_groups (n, 1) = forall ₛ->[n] (spoint f) := idp

Definition ab_group_LES_of_shomotopy_groups : forall (v : +3ℤ), ab_group (LES_of_shomotopy_groups v)
  | (n, fin.mk 0 H) := proof AbGroup.struct (forall ₛ[n] Y) qed
  | (n, fin.mk 1 H) := proof AbGroup.struct (forall ₛ[n] X) qed
  | (n, fin.mk 2 H) := proof AbGroup.struct (forall ₛ[n] (sfiber f)) qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end
  local attribute ab_group_LES_of_shomotopy_groups [instance]

Definition is_mul_hom_LES_of_shomotopy_groups :
    forall (v : +3ℤ), is_mul_hom (cc_to_fn LES_of_shomotopy_groups v)
  | (n, fin.mk 0 H) := proof homomorphism.struct (forall ₛ->[n] f) qed
  | (n, fin.mk 1 H) := proof homomorphism.struct (forall ₛ->[n] (spoint f)) qed
  | (n, fin.mk 2 H) := proof homomorphism.struct
        (homomorphism_LES_of_homotopy_groups_fun (f (2 - n)) (1 => 2) og forall g_glue Y n) qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

Definition is_exact_LES_of_shomotopy_groups : is_exact LES_of_shomotopy_groups :=
Proof.
    apply is_exact_splice, intro n, apply is_exact_LES_of_homotopy_groups,
Defined.


Definition shomotopy_groups : +3ℤ -> AbGroup
  | (n, fin.mk 0 H) := forall ₛ[n] Y
  | (n, fin.mk 1 H) := forall ₛ[n] X
  | (n, fin.mk k H) := forall ₛ[n] (sfiber f)

Definition shomotopy_groups_fun : forall , shomotopy_groups (S v) ->g shomotopy_groups v
  | (n, fin.mk 0 H) := proof forall ₛ->[n] f qed
  | (n, fin.mk 1 H) := proof forall ₛ->[n] (spoint f) qed
  | (n, fin.mk 2 H) := by rexact homomorphism_LES_of_homotopy_groups_fun (f (2 - n)) (nat.succ nat.zero => 2) og
                             forall g_glue Y n
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end
--(homomorphism_LES_of_homotopy_groups_fun (f (2 - n)) (1 => 2) og forall g_glue Y n)

Definition is_contr_shomotopy_group_sfiber {n : ℤ}
    (H1 : is_embedding (forall ₛ->[n] f)) (H2 : is_surjective (forall ₛ->[n+1] f)) :
    is_contr (forall ₛ[n] (sfiber f)) :=
Proof.
    apply @is_contr_of_is_embedding_of_is_surjective +3ℤ LES_of_shomotopy_groups (n, 0),
    exact is_exact_LES_of_shomotopy_groups (n, 1), exact H1, exact H2
Defined.

Definition is_contr_shomotopy_group_sfiber_of_is_equiv {n : ℤ}
    (H1 : is_equiv (forall ₛ->[n] f)) (H2 : is_equiv (forall ₛ->[n+1] f)) :
    is_contr (forall ₛ[n] (sfiber f)) :=
  proof
    is_contr_shomotopy_group_sfiber (is_embedding_of_is_equiv _) (is_surjective_of_is_equiv _)
  qed

Defined. LES


  (* homotopy group of a prespectrum *)

  local attribute agtrunc aghomotopy_group ghomotopy_group gtrunc
Definition pshomotopy_group_hom (n : ℤ) (E : prespectrum) (k : ℕ)
    : forall ag[k + 2] (E (-n + 2 + k)) ->g forall ag[k + 3] (E (-n + 2 + (k + 1))) :=
Proof.
    change forall g[k + 2] (E (-n + 2 + k)) ->g forall g[k + 3] (E (-n + 2 + (k + 1))),
    refine _ og forall ->g[k+2] (glue E _),
    refine (ghomotopy_group_succ_in (k+1) _)^-1ᵍ og _,
    refine homotopy_group_isomorphism_of_pequiv (k+1) _,
    exact (loop_pequiv_loop (pequiv_of_eq (ap E (add.assoc (-n + 2) k 1))))
Defined.

Definition pshomotopy_group (n : ℤ) (E : prespectrum) : AbGroup :=
  group.seq_colim (fun (k : ℕ) => forall ag[k+2] (E (-n + 2 + k))) (pshomotopy_group_hom n E)

  notation `forall ₚₛ[`:95 n:0 `]`:0 := pshomotopy_group n

Definition pshomotopy_group_fun (n : ℤ) {E F : prespectrum} (f : E ->ₛ F) :
    forall ₚₛ[n] E ->g forall ₚₛ[n] F :=
  proof
  group.seq_colim_functor (fun k => forall ->g[k+2] (f (-n + 2 +[ℤ] k)))
    begin
      intro k,
      note sq1 := homotopy_group_homomorphism_psquare (k+2) (ptranspose (smap.glue_square f (-n + 2 +[ℤ] k))),
      note sq2 := homotopy_group_functor_psquare (k+2) (ap1_psquare (ptransport_natural E F f (add.assoc (-n + 2) k 1))) =>
                        exact sorry --sq1 @htyh sq4 @htyh sq3,
    end
  qed

  notation `forall ₚₛ->[`:95 n:0 `]`:0 := pshomotopy_group_fun n


  (* a chain complex of spectra (not yet used anywhere) *)

  structure sp_chain_complex (N : succ_str) : Type :=
    (car : N -> spectrum)
    (fn : forall (n : N), car (S n) ->ₛ car n)
    (is_chain_complex : forall n, fn n oₛ fn (S n) ~ₛ szero _ _)

  section
    variables {N : succ_str} (X : sp_chain_complex N) (n : N)

Definition scc_to_car [coercion] := @sp_chain_complex.car
Definition scc_to_fn : X (S n) ->ₛ X n := sp_chain_complex.fn X n
Definition scc_is_chain_complex : scc_to_fn X n oₛ scc_to_fn X (S n) ~ₛ szero _ _
      := sp_chain_complex.is_chain_complex X n
Defined.


  ------------------------------
    ------------------------------

Definition psp_susp (X : pType) : gen_prespectrum +ℕ :=
    gen_prespectrum.mk (fun n => iterate_susp n X) (fun n => loop_susp_unit (iterate_susp n X))

Definition psp_sphere : gen_prespectrum +ℕ :=
    psp_susp bool.pbool


  (*------------------------------
    Cotensor of spectra by types
  ------------------------------*)


Definition sp_cotensor {N : succ_str} (A : pType) (B : gen_spectrum N) :
    gen_spectrum N :=
    spectrum.MK (fun n => ppMap A (B n))
      (fun n => (loop_ppMap_commute A (B (S n)))^-1ᵉ* o*ᵉ ppMap_pequiv_ppMap_right (equiv_glue B n))

  (* unpointed cotensor *)
Definition sp_ucotensor {N : succ_str} (A : Type) (B : gen_spectrum N) :
    gen_spectrum N :=
  spectrum.MK (fun n => A ->ᵘ* B n)
              (fun n => pumap_pequiv_right A (equiv_glue B n) @e* (loop_pumap A (B (S n)))^-1ᵉ*)

  ----------------------------------------
    ----------------------------------------

Definition spi {N : succ_str} (A : pType) (E : A -> gen_spectrum N) :
    gen_spectrum N :=
  spectrum.MK (fun n => ppforall a, E a n)
    (fun n => !loop_pppi_pequiv^-1ᵉ* o*ᵉ ppi_pequiv_right (fun a => equiv_glue (E a) n))

Definition spi_compose_left {N : succ_str} {A : pType} {E F : A -> gen_spectrum N}
    (f : forall a, E a ->ₛ F a) : spi A E ->ₛ spi A F :=
  smap.mk (fun n => pppi_compose_left (fun a => f a n))
    begin
      intro n,
      exact psquare_pppi_compose_left (fun a => (glue_square (f a) n)) @v*
        (ptranspose !loop_pppi_pequiv_natural_right)^-1ᵛ*
    end

Definition supi {N : succ_str} (A : Type) (E : A -> gen_spectrum N) :
    gen_spectrum N :=
  spectrum.MK (fun n => forall ᵘ*a, E a n)
              (fun n => pupi_pequiv_right (fun a => equiv_glue (E a) n) @e* (loop_pupi (fun a => E a (S n)))^-1ᵉ*)

  (* Mapping spectra *)

  (*
    suspension of a spectrum

    this is just a shift. We could call a shift in the other direction loopn,
    though it might be more convenient to just take a negative suspension
  *)

Definition ssusp {N : succ_str} (X : gen_spectrum N) : gen_spectrum N :=
  spectrum.MK (fun n => X (S n)) (fun n => equiv_glue X (S n))

Definition ssuspn (k : ℤ) (X : spectrum) : spectrum :=
  spectrum.MK (fun n => X (n + k))
              (fun n => equiv_glue X (n + k) @e* loop_pequiv_loop (pequiv_ap X !add.right_comm))

Definition shomotopy_group_ssuspn (k : ℤ) (X : spectrum) (n : ℤ) :
    forall ₛ[k] (ssuspn n X) <~>g forall ₛ[k - n] X :=
  have k - n + (2 - k + n) = 2, from
  !add.comm @
  ap (fun x => x + (k - n)) (!add.assoc @ ap (fun x => 2 + x) (ap (fun x => -k + x) !neg_neg^-1 @ !neg_add^-1)) @
  sub_add_cancel 2 (k - n),
  (shomotopy_group_isomorphism_homotopy_group X this)^-1ᵍ

  (* Tensor by spaces *)

  (* Cofibers and stability *)

  ------------------------------
    ------------------------------

Definition sunit.{u} : spectrum.{u} :=
  spectrum.MK (fun n => plift punit) (fun n => pequiv_of_is_contr _ _ _ _)

Definition shomotopy_group_sunit.{u} (n : ℤ) : forall ₛ[n] sunit.{u} <~>g trivial_ab_group_lift.{u} :=
  phomotopy_group_plift_punit 2

Definition add_point_spectrum {X : Type} (Y : X -> spectrum) (x : X₊) : spectrum :=
  spectrum.MK (fun n => add_point_over (fun x => Y x n) x)
    begin
      intro n, induction x with x,
        apply pequiv_of_is_contr,
          apply is_trunc_lift,
        apply is_contr_loop_of_is_contr, apply is_trunc_lift,
      exact equiv_glue (Y x) n
    end

  open option
Definition shomotopy_group_add_point_spectrum {X : Type} (Y : X -> spectrum) (n : ℤ) :
    forall (x : X₊), forall , forall ₛ[n] (Y x)) x
  | (some x) := by reflexivity
  | none     := proof phomotopy_group_plift_punit 2 qed

  (* The Eilenberg-MacLane spectrum *)

Definition EM_spectrum (*[constructor]*) (G : AbGroup) : spectrum :=
  spectrum.Mk (K G) (fun n => (loop_EM G n)^-1ᵉ*)

Definition EM_spectrum_pequiv {G H : AbGroup} (e : G <~>g H) (n : ℤ) :
    EM_spectrum G n <~>* EM_spectrum H n :=
  spectrum_pequiv_of_nat (fun k => EM_pequiv_EM k e) n

Definition EM_spectrum_trivial.{u} (n : ℤ) :
    EM_spectrum trivial_ab_group_lift.{u} n <~>* trivial_ab_group_lift.{u} :=
  pequiv_of_is_contr _ _
    (is_contr_spectrum_of_nat (fun k => is_contr_EM k !is_trunc_lift) n)
    !is_trunc_lift

Definition is_contr_EM_spectrum_neg (G : AbGroup) (n : ℕ) : is_contr (EM_spectrum G (-[1+n])) :=
Proof.
    induction n with n IH,
    { apply is_contr_loop, exact is_trunc_EM G 0 },
    { apply is_contr_loop_of_is_contr, exact IH }
Defined.

Definition is_contr_EM_spectrum (G : AbGroup) (n : ℤ) (H : is_contr G) : is_contr (EM_spectrum G n) :=
Proof.
    cases n with n n,
    { apply is_contr_EM n H },
    { apply is_contr_EM_spectrum_neg G n }
Defined.

  (* K(forall ₗ(Aₖ),l) <~>* K(forall ₙ(A),l) for l = n + k *)
Definition EM_type_pequiv_EM (A : spectrum) {n k : ℤ} {l : ℕ} (p : n + k = l) :
    EM_type (A k) l <~>* EM (forall ₛ[n] A) l :=
Proof.
    symmetry,
    cases l with l,
    { exact shomotopy_group_pequiv_homotopy_group A p },
    { cases l with l,
      { apply EM1_pequiv_EM1, exact shomotopy_group_isomorphism_homotopy_group A p },
      { apply EMadd1_pequiv_EMadd1 (l+1), exact shomotopy_group_isomorphism_homotopy_group A p }}
Defined.

  (* Wedge of prespectra *)

open fwedge

Definition fwedge_prespectrum.{u v} {I : Type.{v}} (X : I -> prespectrum.{u}) : prespectrum.{max u v} :=
Proof.
    fconstructor,
    { intro n, exact fwedge (fun i => X i n) },
    { intro n, fapply fwedge_pmap,
      intro i, exact Ω-> !pinl o* !glue }
Defined.

Defined. spectrum
