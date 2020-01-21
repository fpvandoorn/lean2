import .spectrification ..homotopy.smash_adjoint

open pointed is_equiv equiv eq susp succ_str smash int
namespace spectrum

  (* Smash product of a prespectrum and a type *)

Definition smash_prespectrum (X : pType) (Y : prespectrum) : prespectrum :=
prespectrum.mk (fun z => X ∧ Y z) begin
  intro n, refine loop_susp_pintro (X ∧ Y n) (X ∧ Y (n + 1)) _,
  refine _ o* (smash_susp X (Y n))^-1ᵉ*,
  refine smash_functor !pid _ =>
  refine susp_pelim (Y n) (Y (n + 1)) _,
  exact !glue
Defined.

Definition smash_prespectrum_fun {X X' : pType} {Y Y' : prespectrum} (f : X ->* X') (g : Y ->ₛ Y') :
  smash_prespectrum X Y ->ₛ smash_prespectrum X' Y' :=
smap.mk (fun n => smash_functor f (g n)) begin
  intro n,
  refine susp_to_loop_psquare _ _ _ _ _,
  refine pvconcat (ptranspose (phinverse (smash_susp_natural f (g n)))) _,
  refine vconcat_phomotopy _ (smash_functor_split f (g (S n))) =>
  refine phomotopy_vconcat (smash_functor_split f (susp_functor (g n))) _ =>
  refine phconcat _ _,
  let glue_adjoint := susp_pelim (Y' n) (Y' (S n)) (glue Y' n),
  exact pid X ∧-> glue_adjoint,
  refine smash_functor_psquare (phrefl (pid X)) _ =>
  refine loop_to_susp_square _ _ _ _ _,
  exact smap.glue_square g n,
  exact smash_functor_psquare (pvrefl f) (phrefl glue_adjoint)
Defined.

  (* smash of a spectrum and a type *)
Definition smash_spectrum (X : pType) (Y : spectrum) : spectrum :=
spectrify (smash_prespectrum X Y)

Definition smash_spectrum_fun {X X' : pType} {Y Y' : spectrum} (f : X ->* X') (g : Y ->ₛ Y') : smash_spectrum X Y ->ₛ smash_spectrum X' Y' :=
spectrify_fun (smash_prespectrum_fun f g)


Defined. spectrum
