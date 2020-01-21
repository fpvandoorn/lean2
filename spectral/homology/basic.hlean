(*
Copyright (c) 2017 Yuri Sulyma, Favonia
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuri Sulyma, Favonia, Floris van Doorn

Reduced homology theories
*)

import ..spectrum.smash ..homotopy.wedge

open eq spectrum int pointed group algebra sphere nat equiv susp is_trunc
  function fwedge cofiber lift is_equiv choice algebra pi smash wedge

namespace homology

  (* homology theory *)
  structure homology_theory.{u} : Type.{u+1}.
  (HH : ℤ -> pType.{u} -> AbGroup.{u})
  (Hh : forall (n : ℤ) {X Y : pType} (f : X ->* Y), HH n X ->g HH n Y)
  (Hpid : forall (n : ℤ) {X : pType} (x : HH n X), Hh n (pid X) x = x)
  (Hpcompose : forall (n : ℤ) {X Y Z : pType} (f : Y ->* Z) (g : X ->* Y),
  Hh n (f o* g) == Hh n f o Hh n g)
  (Hsusp : forall (n : ℤ) (X : pType), HH (succ n) (susp X) <~>g HH n X)
  (Hsusp_natural : forall (n : ℤ) {X Y : pType} (f : X ->* Y),
  Hsusp n Y o Hh (succ n) (susp_functor f) == Hh n f o Hsusp n X)
  (Hexact : forall (n : ℤ) {X Y : pType} (f : X ->* Y), is_exact_g (Hh n f) (Hh n (pcod f)))
  (Hadditive : forall (n : ℤ) {I : Set.{u}} (X : I -> pType), is_equiv
  (dirsum_elim (fun i => Hh n (pinl i)) : dirsum (fun i => HH n (X i)) -> HH n (⋁ X)))

  structure ordinary_homology_theory.{u} extends homology_theory.{u} : Type.{u+1}.
  (Hdimension : forall (n : ℤ), n ≠ 0 -> is_contr (HH n (plift (sphere 0))))

  section
  universe variable u
  parameter (theory : homology_theory.{u})
  open homology_theory

Definition HH_base_indep (n : ℤ) {A : Type} (a b : A)
  : HH theory n (Build_pType A a) <~>g HH theory n (Build_pType A b).
  calc HH theory n (Build_pType A a) <~>g HH theory (int.succ n) (susp A) : by exact (Hsusp theory n (Build_pType A a)) ^-1ᵍ
  ... <~>g HH theory n (Build_pType A b)       : by exact Hsusp theory n (Build_pType A b)

Definition Hh_homotopy' (n : ℤ) {A B : pType} (f : A -> B) (p q : f (point _) = (point _))
  : Hh theory n (Build_pMap f p) == Hh theory n (Build_pMap f q) . fun x =>
  calc       Hh theory n (Build_pMap f p) x
  = Hh theory n (Build_pMap f p) (Hsusp theory n A ((Hsusp theory n A)^-1ᵍ x))
  : by exact ap (Hh theory n (Build_pMap f p)) (equiv.to_right_inv (equiv_of_isomorphism (Hsusp theory n A)) x)^-1
  ... = Hsusp theory n B (Hh theory (succ n) (Build_pMap (susp_functor' f) !refl) ((Hsusp theory n A)^-1 x))
  : by exact (Hsusp_natural theory n (Build_pMap f p) ((Hsusp theory n A)^-1ᵍ x))^-1
  ... = Hh theory n (Build_pMap f q) (Hsusp theory n A ((Hsusp theory n A)^-1 x))
  : by exact Hsusp_natural theory n (Build_pMap f q) ((Hsusp theory n A)^-1 x)
  ... = Hh theory n (Build_pMap f q) x
  : by exact ap (Hh theory n (Build_pMap f q)) (equiv.to_right_inv (equiv_of_isomorphism (Hsusp theory n A)) x)

Definition Hh_homotopy (n : ℤ) {A B : pType} (f g : A ->* B) (h : f == g) : Hh theory n f == Hh theory n g . fun x =>
  calc       Hh theory n f x
  = Hh theory n (Build_pMap f (point_eq f)) x : by exact ap (fun f => Hh theory n f x) (pmap_eta_eq f)^-1
  ... = Hh theory n (Build_pMap f (h (point _) @ point_eq g)) x : by exact Hh_homotopy' n f (point_eq f) (h (point _) @ point_eq g) x
  ... = Hh theory n g x :
Proof.
  apply ap (fun f => Hh theory n f x), apply path_pforall, fapply Build_pHomotopy,
  { exact h },
  reflexivity
Defined.

Definition HH_isomorphism (n : ℤ) {A B : pType} (e : A <~>* B)
  : HH theory n A <~>g HH theory n B.
Proof.
  fapply isomorphism.mk,
  { exact Hh theory n e },
  fapply adjointify,
  { exact Hh theory n e^-1ᵉ* },
  { intro x, exact calc
  Hh theory n e (Hh theory n e^-1ᵉ* x)
  = Hh theory n (e o* e^-1ᵉ*) x : by exact (Hpcompose theory n e e^-1ᵉ* x)^-1
  ... = Hh theory n !pid x : by exact Hh_homotopy n (e o* e^-1ᵉ*) !pid (to_right_inv e) x
  ... = x : by exact Hpid theory n x
  },
  { intro x, exact calc
  Hh theory n e^-1ᵉ* (Hh theory n e x)
  = Hh theory n (e^-1ᵉ* o* e) x : by exact (Hpcompose theory n e^-1ᵉ* e x)^-1
  ... = Hh theory n !pid x : by exact Hh_homotopy n (e^-1ᵉ* o* e) !pid (to_left_inv e) x
  ... = x : by exact Hpid theory n x
  }
Defined.

Definition Hadditive_equiv (n : ℤ) {I : Type} [is_set I] (X : I -> pType)
  : dirsum (fun i => HH theory n (X i)) <~>g HH theory n (⋁ X).
  isomorphism.mk (dirsum_elim (fun i => Hh theory n (fwedge.pinl i))) (Hadditive theory n X)

Definition Hadditive' (n : ℤ) {I : Type₀} [is_set I] (X : I -> pType.{u}) : is_equiv
  (dirsum_elim (fun i => Hh theory n (pinl i)) : dirsum (fun i => HH theory n (X i)) -> HH theory n (⋁ X)).
  let iso3 . HH_isomorphism n (fwedge_down_left.{0 u} X) in
  let iso2 . Hadditive_equiv n (X o down.{0 u}) in
  let iso1 . (dirsum_down_left.{0 u} (fun i => HH theory n (X i)))^-1ᵍ in
  let iso . calc dirsum (fun i => HH theory n (X i))
  <~>g dirsum (fun i => HH theory n (X (down.{0 u} i))) : by exact iso1
  ... <~>g HH theory n (⋁ (X o down.{0 u})) : by exact iso2
  ... <~>g HH theory n (⋁ X) : by exact iso3
  in
Proof.
  fapply is_equiv_of_equiv_of_homotopy,
  { exact equiv_of_isomorphism iso  },
  { refine dirsum_homotopy _, intro i y,
  refine homomorphism_compose_eq iso3 (iso2 og iso1) _ @ _,
  refine ap iso3 (homomorphism_compose_eq iso2 iso1 _) @ _,
  refine ap (iso3 o iso2) _ @ _,
  { exact dirsum_incl (fun i => HH theory n (X (down i))) (up i) y },
  { refine _ @ dirsum_elim_compute (fun i => dirsum_incl (fun i => HH theory n (X (down.{0 u} i))) (up i)) i y,
  reflexivity
  },
  refine ap iso3 _ @ _,
  { exact Hh theory n (fwedge.pinl (up i)) y },
  { refine _ @ dirsum_elim_compute (fun i => Hh theory n (fwedge.pinl i)) (up i) y,
  reflexivity
  },
  refine (Hpcompose theory n (fwedge_down_left X) (fwedge.pinl (up i)) y)^-1 @ _,
  refine Hh_homotopy n (fwedge_down_left.{0 u} X o* fwedge.pinl (up i)) (fwedge.pinl i) (fwedge_pmap_beta (fun i => pinl (down i)) (up i)) y @ _,
  refine (dirsum_elim_compute (fun i => Hh theory n (pinl i)) i y)^-1
  }
Defined.

Definition Hadditive'_equiv (n : ℤ) {I : Type₀} [is_set I] (X : I -> pType)
  : dirsum (fun i => HH theory n (X i)) <~>g HH theory n (⋁ X).
  isomorphism.mk (dirsum_elim (fun i => Hh theory n (fwedge.pinl i))) (Hadditive' n X)

Definition Hfwedge (n : ℤ) {I : Type} [is_set I] (X : I -> pType): HH theory n (⋁ X) <~>g dirsum (fun i => HH theory n (X i)).
  (isomorphism.mk _ (Hadditive theory n X))^-1ᵍ

Definition Hwedge (n : ℤ) (A B : pType) : HH theory n (wedge A B) <~>g HH theory n A \*g HH theory n B.
  calc HH theory n (A ∨ B) <~>g HH theory n (⋁ (bool.rec A B)) : by exact HH_isomorphism n (wedge_pequiv_fwedge A B)
  ... <~>g dirsum (fun b => HH theory n (bool.rec A B b)) : by exact (Hadditive'_equiv n (bool.rec A B))^-1ᵍ
  ... <~>g dirsum (bool.rec (HH theory n A) (HH theory n B)) : by exact dirsum_isomorphism (bool.rec !isomorphism.refl !isomorphism.refl)
  ... <~>g HH theory n A \*g HH theory n B : by exact binary_dirsum (HH theory n A) (HH theory n B)

Defined.
  section
  universe variables u v
  parameter (theory : homology_theory.{max u v})
  open homology_theory

Definition Hplift_susp (n : ℤ) (A : pType): HH theory (n + 1) (plift.{u v} (susp A)) <~>g HH theory n (plift.{u v} A).
  calc HH theory (n + 1) (plift.{u v} (susp A)) <~>g HH theory (n + 1) (susp (plift.{u v} A)) : by exact HH_isomorphism theory (n + 1) (plift_susp _)
  ... <~>g HH theory n (plift.{u v} A) : by exact Hsusp theory n (plift.{u v} A)

Definition Hplift_wedge (n : ℤ) (A B : pType): HH theory n (plift.{u v} (A ∨ B)) <~>g HH theory n (plift.{u v} A) \*g HH theory n (plift.{u v} B).
  calc HH theory n (plift.{u v} (A ∨ B)) <~>g HH theory n (plift.{u v} A ∨ plift.{u v} B) : by exact HH_isomorphism theory n (plift_wedge A B)
  ... <~>g HH theory n (plift.{u v} A) \*g HH theory n (plift.{u v} B) : by exact Hwedge theory n (plift.{u v} A) (plift.{u v} B)

Definition Hplift_isomorphism (n : ℤ) {A B : pType} (e : A <~>* B) : HH theory n (plift.{u v} A) <~>g HH theory n (plift.{u v} B).
  HH_isomorphism theory n (!pequiv_plift^-1ᵉ* @e* e @e* !pequiv_plift)

Defined.

(* homology theory associated to a prespectrum *)
Definition homology (X : pType) (E : prespectrum) (n : ℤ) : AbGroup.
pshomotopy_group n (smash_prespectrum X E)

(* an alternativeDefinition, which might be a bit harder to work with *)
Definition homology_spectrum (X : pType) (E : spectrum) (n : ℤ) : AbGroup.
shomotopy_group n (smash_spectrum X E)

Definition parametrized_homology {X : pType} (E : X -> spectrum) (n : ℤ) : AbGroup.
sorry

Definition ordinary_homology (X : pType) (G : AbGroup) (n : ℤ) : AbGroup.
homology X (EM_spectrum G) n

Definition ordinary_homology_Z (X : pType) (n : ℤ) : AbGroup.
ordinary_homology X agℤ n

notation `H_` n `[`:0 X:0 `, ` E:0 `]`:0 . homology X E n
notation `H_` n `[`:0 X:0 `]`:0 . ordinary_homology_Z X n
notation `pH_` n `[`:0 binders `, ` r:(scoped E, parametrized_homology E n) `]`:0 . r

Definition unpointed_homology (X : Type) (E : spectrum) (n : ℤ) : AbGroup.
H_ n[X₊, E]

Definition homology_functor {X Y : pType} {E F : prespectrum} (f : X ->* Y)
  (g : E ->ₛ F) (n : ℤ) : homology X E n ->g homology Y F n.
pshomotopy_group_fun n (smash_prespectrum_fun f g)

Definition homology_theory_spectrum_is_exact.{u} (E : spectrum.{u}) (n : ℤ) {X Y : pType}
  (f : X ->* Y) : is_exact_g (homology_functor f (sid E) n) (homology_functor (pcod f) (sid E) n).
Proof.
  exact sorry
Defined.

Definition homology_theory_spectrum.{u} (E : spectrum.{u}) : homology_theory.{u}.
Proof.
  fapply homology_theory.mk,
  exact (fun n X => H_ n[X, E]),
  exact (fun n X Y f => homology_functor f (sid E) n) =>
  exact sorry,   exact sorry,
  exact sorry,
  exact sorry,
  apply homology_theory_spectrum_is_exact,
  exact sorry
Defined.
Defined. homology
