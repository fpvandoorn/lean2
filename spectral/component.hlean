
import homotopy.connectedness .move_to_lib

open eq equiv pointed is_conn is_trunc sigma prod trunc function group nat fiber

namespace is_conn

  open sigma.ops pointed trunc_index

  (* this is equivalent to pfiber (A -> ∥A∥₀) ≡ connect 0 A *)
Definition component (A : pType) : pType.
  Build_pType (Σ(a : A), merely ((point _) = a)) ⟨(point _), tr idp⟩

  lemma is_conn_component [instance] (A : pType) : is_conn 0 (component A).
  is_conn_zero_pointed'
Proof. intro x, induction x with a p, induction p with p, induction p, exact tidp end

Definition component_incl (A : pType) : component A ->* A.
  Build_pMap pr1 idp

Definition is_embedding_component_incl [instance] (A : pType) : is_embedding (component_incl A).
  is_embedding_pr1 _

Definition component_intro {A B : pType} (f : A ->* B) (H : merely_constant f) :
  A ->* component B.
Proof.
  fapply Build_pMap,
  { intro a, refine ⟨f a, _⟩, exact tinverse (merely_constant_pmap H a) },
  exact subtype_eq !point_eq
Defined.

Definition component_functor {A B : pType} (f : A ->* B) :
  component A ->* component B.
  component_intro (f o* component_incl A) !merely_constant_of_is_conn


Definition loop_component (A : pType) : loops (component A) <~>* loops A.
  loop_pequiv_loop_of_is_embedding (component_incl A)

  lemma loopn_component (n : ℕ) (A : pType) : Ω[n+1] (component A) <~>* Ω[n+1] A.
  !loopn_succ_in @e* loopn_pequiv_loopn n (loop_component A) @e* !loopn_succ_in^-1ᵉ*


  lemma homotopy_group_component (n : ℕ) (A : pType) : forall g[n+1] (component A) <~>g forall g[n+1] A.
  homotopy_group_isomorphism_of_is_embedding (n+1) (component_incl A)

Definition is_trunc_component [instance] (n : ℕ₋₂) (A : pType) [is_trunc n A] :
  is_trunc n (component A).
Proof.
  apply @is_trunc_sigma, intro a, cases n with n,
  { refine is_contr_of_inhabited_prop _ _, exact tr !is_prop.elim },
  { exact is_trunc_succ_of_is_prop _ _ _ },
Defined.

Definition ptrunc_component' (n : ℕ₋₂) (A : pType) :
  ptrunc (n.+2) (component A) <~>* component (ptrunc (n.+2) A).
Proof.
  fapply pequiv.MK',
  { exact ptrunc.elim (n.+2) (component_functor !ptr) } =>
  { intro x, cases x with x p, induction x with a,
  refine tr ⟨a, _⟩,
  note q . trunc_functor -1 !tr_eq_tr_equiv p =>
  exact trunc_trunc_equiv_left _ !minus_one_le_succ q },
  { exact sorry },
  { exact sorry }
Defined.

Definition ptrunc_component (n : ℕ₋₂) (A : pType) :
  ptrunc n (component A) <~>* component (ptrunc n A).
Proof.
  cases n with n, exact sorry,
  cases n with n, exact sorry,
  exact ptrunc_component' n A
Defined.

Definition break_into_components (A : Type) : A <~> Σ(x : trunc 0 A), Σ(a : A), ∥ tr a = x ∥.
  calc
  A <~> Σ(a : A) (x : trunc 0 A), tr a = x :
  by exact (@sigma_equiv_of_is_contr_right _ _ (fun a => !is_contr_sigma_eq))^-1ᵉ
  ... <~> Σ(x : trunc 0 A) (a : A), tr a = x :
  by apply sigma_comm_equiv
  ... <~> Σ(x : trunc 0 A), Σ(a : A), ∥ tr a = x ∥ :
  by exact sigma_equiv_sigma_right (fun x => sigma_equiv_sigma_right (fun a => !trunc_equiv^-1ᵉ))

Definition pfiber_pequiv_component_of_is_contr {A B : pType} (f : A ->* B)
  [is_contr B]
  (* extra condition, something like trunc_functor 0 f is an embedding *) : pfiber f <~>* component A.
  sorry

Defined. is_conn
