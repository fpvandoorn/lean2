import .basic ..colimit.pointed

open eq pointed succ_str is_equiv equiv spectrum.smap seq_colim nat

namespace spectrum

  (* Prespectrification *)
Definition is_sconnected {N : succ_str} {X Y : gen_prespectrum N} (h : X ->ₛ Y) : Type :=
  forall (E : gen_spectrum N), is_equiv (fun g : Y ->ₛ E => g oₛ h)

Definition prespectrification {N : succ_str} (X : gen_prespectrum N) : gen_prespectrum N :=
  gen_prespectrum.mk (fun n => loops (X (S n))) (fun n => Ω-> (glue X (S n)))

Definition to_prespectrification_pfun {N : succ_str} (X : gen_prespectrum N) (n : N) : X n ->* prespectrification X n :=
  glue X n

Definition to_prespectrification_psq {N : succ_str} (X : gen_prespectrum N) (n : N) :
  psquare (to_prespectrification_pfun X n) (Ω-> (to_prespectrification_pfun X (S n))) (glue X n)
    (glue (prespectrification X) n) :=
  psquare_of_phomotopy (reflexivity _)

Definition to_prespectrification {N : succ_str} (X : gen_prespectrum N) : X ->ₛ prespectrification X :=
Proof.
    fapply smap.mk,
    exact to_prespectrification_pfun X =>
    exact to_prespectrification_psq X,
Defined.

Definition is_sequiv_smap_to_prespectrification_of_is_spectrum {N : succ_str} (E : gen_prespectrum N) (H : is_spectrum E) : is_sequiv_smap (to_prespectrification E) :=
Proof.
    intro n, induction E, induction H, exact is_equiv_glue n,
Defined.

Definition is_spectrum_of_is_sequiv_smap_to_prespectrification {N : succ_str} (E : gen_prespectrum N) (H : is_sequiv_smap (to_prespectrification E)) : is_spectrum E :=
Proof.
    fapply is_spectrum.mk,
    exact H
Defined.


Definition is_sconnected_to_prespectrification_inv_pfun {N : succ_str} {X : gen_prespectrum N} {E : gen_spectrum N} : (X ->ₛ E) -> forall , prespectrification X n ->* E n :=
  fun (f : X ->ₛ E) n => (equiv_glue E n)^-1ᵉ* o* Ω-> (f (S n))

Definition is_sconnected_to_prespectrification_inv_psq {N : succ_str} {X : gen_prespectrum N} {E : gen_spectrum N} (f : X ->ₛ E) (n : N) :
  psquare (is_sconnected_to_prespectrification_inv_pfun f n)
      (Ω-> (is_sconnected_to_prespectrification_inv_pfun f (S n)))
      (glue (prespectrification X) n)
      (glue (gen_spectrum.to_prespectrum E) n)
  :=
Proof.
    fapply psquare_of_phomotopy,
    refine (passoc (glue (gen_spectrum.to_prespectrum E) n) (pequiv.to_pmap
    (equiv_glue (gen_spectrum.to_prespectrum E) n)^-1ᵉ*) (Ω-> (to_fun f (S n))))^-1* @* _ =>
    refine pwhisker_right (Ω-> (to_fun f (S n))) (pright_inv (equiv_glue E n)) @* _ =>
    refine _ @* pwhisker_right (glue (prespectrification X) n) ((ap1_pcompose (pequiv.to_pmap (equiv_glue (gen_spectrum.to_prespectrum E) (S n))^-1ᵉ*) (Ω-> (to_fun f (S (S n)))))^-1*) =>
    refine pid_pcompose (Ω-> (f (S n))) @* _,
    repeat exact sorry
Defined.

Definition is_sconnected_to_prespectrification_inv {N : succ_str} (X : gen_prespectrum N) (E : gen_spectrum N)
  : (X ->ₛ E) -> (prespectrification X ->ₛ E) :=
Proof.
    intro f,
    fapply smap.mk,
    exact is_sconnected_to_prespectrification_inv_pfun f =>
    exact is_sconnected_to_prespectrification_inv_psq f
Defined.

Definition is_sconnected_to_prespectrification_isretr_pfun {N : succ_str} {X : gen_prespectrum N} {E : gen_spectrum N} (f : prespectrification X ->ₛ E) (n : N) : to_fun (is_sconnected_to_prespectrification_inv X E (f oₛ to_prespectrification X)) n ==* to_fun f n := begin exact sorry end

Definition is_sconnected_to_prespectrification_isretr_psq {N : succ_str} {X : gen_prespectrum N} {E : gen_spectrum N} (f : prespectrification X ->ₛ E) (n : N) :
  ptube_v (is_sconnected_to_prespectrification_isretr_pfun f n)
      (Ω⇒ (is_sconnected_to_prespectrification_isretr_pfun f (S n)))
      (glue_square (is_sconnected_to_prespectrification_inv X E (f oₛ to_prespectrification X)) n)
      (glue_square f n)
  :=
Proof.
    repeat exact sorry
Defined.

Definition is_sconnected_to_prespectrification_isretr {N : succ_str} (X : gen_prespectrum N) (E : gen_spectrum N) (f : prespectrification X ->ₛ E) : is_sconnected_to_prespectrification_inv X E (f oₛ to_prespectrification X) = f :=
Proof.
    fapply eq_of_shomotopy,
    fapply shomotopy.mk,
    exact is_sconnected_to_prespectrification_isretr_pfun f =>
    exact is_sconnected_to_prespectrification_isretr_psq f,
Defined.

Definition is_sconnected_to_prespectrification_issec_pfun {N : succ_str} {X : gen_prespectrum N} {E : gen_spectrum N} (g : X ->ₛ E) (n : N) :
  to_fun (is_sconnected_to_prespectrification_inv X E g oₛ to_prespectrification X) n ==* to_fun g n
  :=
Proof.
    repeat exact sorry
Defined.

Definition is_sconnected_to_prespectrification_issec_psq {N : succ_str} {X : gen_prespectrum N} {E : gen_spectrum N} (g : X ->ₛ E) (n : N) :
  ptube_v (is_sconnected_to_prespectrification_issec_pfun g n)
      (Ω⇒ (is_sconnected_to_prespectrification_issec_pfun g (S n)))
      (glue_square (is_sconnected_to_prespectrification_inv X E g oₛ to_prespectrification X) n)
      (glue_square g n)
  :=
Proof.
    repeat exact sorry
Defined.

Definition is_sconnected_to_prespectrification_issec {N : succ_str} (X : gen_prespectrum N) (E : gen_spectrum N) (g : X ->ₛ E) :
  is_sconnected_to_prespectrification_inv X E g oₛ to_prespectrification X = g :=
Proof.
    fapply eq_of_shomotopy,
    fapply shomotopy.mk,
    exact is_sconnected_to_prespectrification_issec_pfun g =>
    exact is_sconnected_to_prespectrification_issec_psq g,
Defined.

Definition is_sconnected_to_prespectrify {N : succ_str} (X : gen_prespectrum N) :
    is_sconnected (to_prespectrification X) :=
Proof.
    intro E,
    fapply adjointify,
    exact is_sconnected_to_prespectrification_inv X E,
    exact is_sconnected_to_prespectrification_issec X E,
    exact is_sconnected_to_prespectrification_isretr X E
Defined.

Definition is_spectrum_of_local (X : gen_prespectrum +ℕ) (Hyp : is_equiv (fun (f : prespectrification (psp_sphere) ->ₛ X) => f oₛ to_prespectrification (psp_sphere))) : is_spectrum X :=
Proof.
    fapply is_spectrum.mk,
    exact sorry
Defined.

  (* Spectrification *)

  open chain_complex
Definition spectrify_type_term {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ) : pType :=
  Ω[k] (X (n +' k))

Definition spectrify_type_fun' {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ) :
    Ω[k] (X n) ->* Ω[k+1] (X (S n)) :=
  !loopn_succ_in^-1ᵉ* o* Ω->[k] (glue X n)

Definition spectrify_type_fun {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ) :
    spectrify_type_term X n k ->* spectrify_type_term X n (k+1) :=
  spectrify_type_fun' X (n +' k) k

Definition spectrify_type_fun_zero {N : succ_str} (X : gen_prespectrum N) (n : N) :
    spectrify_type_fun X n 0 ==* glue X n :=
  !pid_pcompose

Definition spectrify_type {N : succ_str} (X : gen_prespectrum N) (n : N) : pType :=
  pseq_colim (spectrify_type_fun X n)

  (*
    Let Y = spectify X ≡ colim_k Ω^k X (n + k). Then
    loops Y (n+1) ≡ loops colim_k Ω^k X ((n + 1) + k)
          ... = colim_k Ω^{k+1} X ((n + 1) + k)
          ... = colim_k Ω^{k+1} X (n + (k + 1))
          ... = colim_k Ω^k X(n + k)
          ... ≡ Y n
  *)

Definition spectrify_type_fun'_succ {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ) :
    spectrify_type_fun' X n (succ k) ==* Ω-> (spectrify_type_fun' X n k) :=
Proof.
    refine !ap1_pcompose^-1*
Defined.

Definition spectrify_pequiv {N : succ_str} (X : gen_prespectrum N) (n : N) :
    spectrify_type X n <~>* loops (spectrify_type X (S n)) :=
Proof.
    refine !pshift_equiv @e* _,
    transitivity pseq_colim (fun k => spectrify_type_fun' X (S n +' k) (succ k)) =>
    fapply pseq_colim_pequiv,
    { intro n, apply loopn_pequiv_loopn, apply pequiv_ap X, apply succ_str.add_succ },
    { exact abstract begin intro k,
      refine !passoc^-1* @* _, refine pwhisker_right _ (loopn_succ_in_inv_natural (succ k) _) @* _,
      refine !passoc @* _ @* !passoc^-1*, apply pwhisker_left,
      refine !apn_pcompose^-1* @* _ @* !apn_pcompose, apply apn_phomotopy,
      exact !glue_ptransport^-1* end end },
    refine _ @e* !pseq_colim_loop^-1ᵉ*,
    exact pseq_colim_equiv_constant (fun n => !spectrify_type_fun'_succ) =>
Defined.

Definition spectrify {N : succ_str} (X : gen_prespectrum N) : gen_spectrum N :=
  spectrum.MK (spectrify_type X) (spectrify_pequiv X)

Definition spectrify_map {N : succ_str} {X : gen_prespectrum N} : X ->ₛ spectrify X :=
Proof.
    fapply smap.mk,
    { intro n, exact pinclusion _ 0 },
    { intro n, apply phomotopy_of_psquare,
      refine !pid_pcompose^-1* @ph* _,
      refine !passoc @* pwhisker_left _ (pshift_equiv_pinclusion (spectrify_type_fun X n) 0) @* _ =>
      refine !passoc^-1* @* _,
      refine _ ◾* (spectrify_type_fun_zero X n @* !pid_pcompose^-1*) =>
      refine !passoc @* pwhisker_left _ !pseq_colim_pequiv_pinclusion @* _,
      refine pwhisker_left _ (pwhisker_left _ (ap1_pid) @* !pcompose_pid) @* _,
      refine !passoc @* pwhisker_left _ !seq_colim_equiv_constant_pinclusion @* _,
      apply pinv_left_phomotopy_of_phomotopy,
      exact !pseq_colim_loop_pinclusion^-1*
    }
Defined.

Definition spectrify.elim_n {N : succ_str} {X : gen_prespectrum N} {Y : gen_spectrum N}
    (f : X ->ₛ Y) (n : N) : (spectrify X) n ->* Y n :=
Proof.
    fapply pseq_colim.elim,
    { intro k, refine !equiv_gluen^-1ᵉ* o* apn k (f (n +' k)) },
    { intro k, refine !passoc @* pwhisker_right _ !equiv_gluen_inv_succ @* _,
      refine !passoc @* _, apply pwhisker_left,
      refine !passoc @* _,
      refine pwhisker_left _ ((passoc _ _ (_ o* _))^-1*) @* _,
      refine pwhisker_left _ !passoc^-1* @* _,
      refine pwhisker_left _ (pwhisker_right _ (phomotopy_pinv_right_of_phomotopy (!loopn_succ_in_natural))^-1*) @* _,
      refine pwhisker_right _ !apn_pinv @* _,
      refine (phomotopy_pinv_left_of_phomotopy _)^-1*,
      refine apn_psquare k _,
      refine psquare_of_phomotopy !smap.glue_square }
Defined.

Definition spectrify.elim {N : succ_str} {X : gen_prespectrum N} {Y : gen_spectrum N}
    (f : X ->ₛ Y) : spectrify X ->ₛ Y :=
Proof.
    fapply smap.mk,
    { intro n, exact spectrify.elim_n f n },
    { intro n, exact sorry }
Defined.

Definition phomotopy_spectrify.elim {N : succ_str} {X : gen_prespectrum N} {Y : gen_spectrum N}
    (f : X ->ₛ Y) (n : N) : spectrify.elim_n f n o* spectrify_map n ==* f n :=
Proof.
    refine pseq_colim.elim_pinclusion _ _ 0 @* _,
    exact !pid_pcompose
Defined.

Definition spectrify_fun {N : succ_str} {X Y : gen_prespectrum N} (f : X ->ₛ Y) : spectrify X ->ₛ spectrify Y :=
  spectrify.elim ((@spectrify_map _ Y) oₛ f)


Defined. spectrum
