(*
Copyright (c) 2014-2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Early library ported from Coq HoTT, but greatly extended since.
The basicDefinitions are in init.pointed

See also .pointed2
*)

import .nat.basic ..arity ..prop_trunc
open is_trunc eq prod sigma nat equiv option is_equiv bool unit sigma.ops sum algebra function

namespace pointed
  variables {A B : Type}

Definition pointed_loop [instance] (a : A) : pointed (a = a).
  pointed.mk idp

Definition pointed_fun_closed (f : A -> B) [H : pointed A] : pointed B.
  pointed.mk (f (point _))

Definition loop (A : pType) : pType.
  pointed.mk' (point A = point A)

Definition loopn : ℕ -> pType -> pType
  | loopn  0    X . X
  | loopn (n+1) X . loop (loopn n X)

  notation `Ω` . loop
  notation `Ω[`:95 n:0 `]`:0 . loopn n

  namespace ops
  (* this is in a separate namespace because it caused type class inference to loop in some places *)
Definition is_trunc_pointed_MK [instance] [priority 1100] (n : ℕ₋₂) {A : Type} (a : A)
  [H : is_trunc n A] : is_trunc n (pointed.MK A a).
  H
Defined. ops

Definition is_trunc_loop [instance] [priority 1100] (A : pType)
  (n : ℕ₋₂) [H : is_trunc (n.+1) A] : is_trunc n (loops A).
  !is_trunc_eq

Definition loopn_zero_eq [unfold_full] (A : pType)
  : Ω[0] A = A . rfl

Definition loopn_succ_eq [unfold_full] (k : ℕ) (A : pType)
  : Ω[succ k] A = loops (Ω[k] A) . rfl

Definition rfln  {n : ℕ} {A : pType} : Ω[n] A . pt
Definition refln (n : ℕ) (A : pType) : Ω[n] A . pt
Definition refln_eq_refl [unfold_full] (A : pType) (n : ℕ) : rfln = rfl :> Ω[succ n] A . rfl

Definition loopn_space (A : Type) [H : pointed A] (n : ℕ) : Type.
  Ω[n] (pointed.mk' A)

Definition loop_mul {k : ℕ} {A : pType} (mul : A -> A -> A) : Ω[k] A -> Ω[k] A -> Ω[k] A.
Proof. cases k with k, exact mul, exact concat end

Definition pType_eq {A B : pType} (f : A <~> B) (p : f (point _) = (point _)) : A = B.
Proof.
  cases A with A a, cases B with B b, esimp at *,
  fapply apdt011 @Build_pType,
  { apply ua f},
  { rewrite [cast_ua, p]},
Defined.

Definition pType_eq_elim {A B : pType} (p : A = B :> pType)
  : Σ(p : carrier A = carrier B :> Type), Point A =[p] Point B.
  by induction p; exact ⟨idp, idpo⟩

  protectedDefinition pType.sigma_char.{u} : pType.{u} <~> Σ(X : Type.{u}), X.
Proof.
  fapply equiv.MK,
  { intro x, induction x with X x, exact ⟨X, x⟩},
  { intro x, induction x with X x, exact pointed.MK X x},
  { intro x, induction x with X x, reflexivity},
  { intro x, induction x with X x, reflexivity},
Defined.

Definition pType.eta_expand (A : pType) : pType.
  pointed.MK A pt

Definition add_point (A : Type) : pType.
  pointed.Mk (none : option A)
  postfix `₊`:(max+1) . add_point
  (* the inclusion A -> A₊ is called "some", the extra point "(point _)" or "none" ("@none A") *)
Defined. pointed

namespace pointed
  (* truncated pointed types *)
Definition ptrunctype_eq {n : ℕ₋₂} {A B : n-pType}
  (p : A = B :> Type) (q : Point A =[p] Point B) : A = B.
Proof.
  induction A with A HA a, induction B with B HB b, esimp at *,
  induction q, esimp,
  refine ap010 (ptrunctype.mk A) _ a,
  exact !is_prop.elim
Defined.

Definition ptrunctype_eq_of_pType_eq {n : ℕ₋₂} {A B : n-pType} (p : A = B :> pType)
  : A = B.
Proof.
  cases pType_eq_elim p with q r,
  exact ptrunctype_eq q r
Defined.

Definition is_trunc_ptrunctype [instance] {n : ℕ₋₂} (A : n-pType) : is_trunc n A.
  trunctype.struct A

Defined. pointed open pointed

namespace pointed
  variables {A B C D : pType} {f g h : A ->* B} {P : A -> Type} {p₀ : P (point _)} {k k' l m : ppi P p₀}

  (* categorical properties of pointed maps *)

Definition pid [refl] (A : pType) : A ->* A.
  Build_pMap id idp

Definition pcompose [trans] {A B C : pType} (g : B ->* C) (f : A ->* B) : A ->* C.
  Build_pMap (fun a => g (f a)) (ap g (point_eq f) @ point_eq g)

  infixr ` o* `:60 . pcompose

Definition pmap_of_map {A B : Type} (f : A -> B) (a : A) :
  pointed.MK A a ->* pointed.MK B (f a).
  Build_pMap f idp

Definition point_eq_pcompose {A B C : pType} (g : B ->* C) (f : A ->* B)
  : point_eq (g o* f) = ap g (point_eq f) @ point_eq g.
  idp

Definition passoc (h : C ->* D) (g : B ->* C) (f : A ->* B) : (h o* g) o* f ==* h o* (g o* f).
  Build_pHomotopy (fun a => idp)
  abstract (concat_1p _) @ whisker_right _ ((ap_pp _ _ _) @ whisker_right _ !ap_compose'^-1) @ (concat_pp_p _ _ _) end

Definition pid_pcompose (f : A ->* B) : pid B o* f ==* f.
Proof.
  fapply Build_pHomotopy,
  { intro a, reflexivity},
  { reflexivity}
Defined.

Definition pcompose_pid (f : A ->* B) : f o* pid A ==* f.
Proof.
  fapply Build_pHomotopy,
  { intro a, reflexivity},
  { reflexivity}
Defined.

  (* equivalences and equalities *)

  protectedDefinition ppi.sigma_char {A : pType} (B : A -> Type) (b₀ : B (point _)) :
  ppi B b₀ <~> Σ(k : forall a, B a), k (point _) = b₀.
Proof.
  fapply equiv.MK: intro x,
  { constructor, exact point_eq x },
  { induction x, constructor, assumption },
  { induction x, reflexivity },
  { induction x, reflexivity }
Defined.

Definition pmap.sigma_char {A B : pType} : (A ->* B) <~> Σ(f : A -> B), f (point _) = (point _).
  !ppi.sigma_char

Definition pmap.eta_expand {A B : pType} (f : A ->* B) : A ->* B.
  Build_pMap f (point_eq f)

Definition pmap_equiv_right (A : pType) (B : Type)
  : (Σ(b : B), A ->* (pointed.Mk b)) <~> (A -> B).
Proof.
  fapply equiv.MK,
  { intro u a, exact pmap.to_fun u.2 a} =>
  { intro f, refine ⟨f (point _), _⟩, fapply Build_pMap,
  intro a, esimp, exact f a,
  reflexivity},
  { intro f, reflexivity},
  { intro u, cases u with b f, cases f with f p, esimp at *, induction p,
  reflexivity}
Defined.

  (* some specific pointed maps *)

  (* The constant pointed map between any two types *)
Definition pconst (A B : pType) : A ->* B.
  !ppi_const

  (* the pointed type of pointed maps (* TODO: remove *) *)
Definition ppMap (A B : pType) : pType.
  @pppi A (fun a => B)

Definition pcast {A B : pType} (p : A = B) : A ->* B.
  Build_pMap (cast (ap pType.carrier p)) (by induction p; reflexivity)

Definition pinverse {X : pType} : loops X ->* loops X.
  Build_pMap eq.inverse idp

  (*
  we generalize theDefinition of ap1 to arbitrary paths, so that we can prove properties about it
  using path induction (see for example ap1_gen_con and ap1_gen_con_natural)
  *)
Definition ap1_gen [unfold 6 9 10] {A B : Type} (f : A -> B) {a a' : A}
  {b b' : B} (q : f a = b) (q' : f a' = b') (p : a = a') : b = b'.
  q^-1 @ ap f p @ q'

Definition ap1_gen_idp {A B : Type} (f : A -> B) {a : A} {b : B} (q : f a = b) :
  ap1_gen f q q idp = idp.
  con.left_inv q

Definition ap1_gen_idp_left {A B : Type} (f : A -> B) {a a' : A} (p : a = a') :
  ap1_gen f idp idp p = ap f p.
  proof idp_con (ap f p) qed

Definition ap1_gen_idp_left_con {A B : Type} (f : A -> B) {a : A} (p : a = a) (q : ap f p = idp) :
  ap1_gen_idp_left f p @ q = proof ap (concat idp) q qed.
  proof idp_con_idp q qed

Definition ap1 (f : A ->* B) : loops A ->* loops B.
  Build_pMap (fun p => ap1_gen f (point_eq f) (point_eq f) p) (ap1_gen_idp f (point_eq f))

Definition apn (n : ℕ) (f : A ->* B) : Ω[n] A ->* Ω[n] B.
Proof.
  induction n with n IH,
  { exact f},
  { esimp [loopn], exact ap1 IH}
Defined.

  notation `Ω->`:(max+5) . ap1
  notation `Ω->[`:95 n:0 `]`:0 . apn n

Definition ptransport {A : Type} (B : A -> pType) {a a' : A} (p : a = a')
  : B a ->* B a'.
  Build_pMap (transport B p) (apdt (fun a => Point (B a)) p)

Definition pmap_of_eq_pt {A : Type} {a a' : A} (p : a = a') :
  pointed.MK A a ->* pointed.MK A a'.
  Build_pMap id p

Definition pbool_pmap {A : pType} (a : A) : pbool ->* A.
  Build_pMap (bool.rec (point _) a) idp

  (* properties of pointed maps *)

Definition apn_zero [unfold_full] (f : A ->* B) : Ω->[0] f = f . idp
Definition apn_succ [unfold_full] (n : ℕ) (f : A ->* B) : Ω->[n + 1] f = Ω-> (Ω->[n] f) . idp

Definition ap1_gen_con {A B : Type} (f : A -> B) {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
  (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (q₃ : f a₃ = b₃) (p₁ : a₁ = a₂) (p₂ : a₂ = a₃) :
  ap1_gen f q₁ q₃ (p₁ @ p₂) = ap1_gen f q₁ q₂ p₁ @ ap1_gen f q₂ q₃ p₂.
Proof. induction p₂, induction q₃, induction q₂, reflexivity end

Definition ap1_gen_inv {A B : Type} (f : A -> B) {a₁ a₂ : A}
  {b₁ b₂ : B} (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (p₁ : a₁ = a₂) :
  ap1_gen f q₂ q₁ p₁^-1 = (ap1_gen f q₁ q₂ p₁)^-1.
Proof. induction p₁, induction q₁, induction q₂, reflexivity end

Definition ap1_con {A B : pType} (f : A ->* B) (p q : loops A) : ap1 f (p @ q) = ap1 f p @ ap1 f q.
  ap1_gen_con f (point_eq f) (point_eq f) (point_eq f) p q

Definition ap1_inv (f : A ->* B) (p : loops A) : ap1 f p^-1 = (ap1 f p)^-1.
  ap1_gen_inv f (point_eq f) (point_eq f) p

  (* the following two facts are used for the suspension axiom to define spectrum cohomology *)
Definition ap1_gen_con_natural {A B : Type} (f : A -> B) {a₁ a₂ a₃ : A} {p₁ p₁' : a₁ = a₂}
  {p₂ p₂' : a₂ = a₃}
  {b₁ b₂ b₃ : B} (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (q₃ : f a₃ = b₃)
  (r₁ : p₁ = p₁') (r₂ : p₂ = p₂') :
  square (ap1_gen_con f q₁ q₂ q₃ p₁ p₂)
  (ap1_gen_con f q₁ q₂ q₃ p₁' p₂')
  (ap (ap1_gen f q₁ q₃) (r₁ ◾ r₂))
  (ap (ap1_gen f q₁ q₂) r₁ ◾ ap (ap1_gen f q₂ q₃) r₂).
Proof. induction r₁, induction r₂, exact vrfl end

Definition ap1_gen_con_idp {A B : Type} (f : A -> B) {a : A} {b : B} (q : f a = b) :
  ap1_gen_con f q q q idp idp @ con.left_inv q ◾ con.left_inv q = con.left_inv q.
  by induction q; reflexivity

Definition apn_con (n : ℕ) (f : A ->* B) (p q : Ω[n+1] A)
  : apn (n+1) f (p @ q) = apn (n+1) f p @ apn (n+1) f q.
  ap1_con (apn n f) p q

Definition apn_inv (n : ℕ)  (f : A ->* B) (p : Ω[n+1] A) : apn (n+1) f p^-1 = (apn (n+1) f p)^-1.
  ap1_inv (apn n f) p

Definition is_equiv_ap1 (f : A ->* B) [is_equiv f] : is_equiv (ap1 f).
Proof.
  induction B with B b, induction f with f pf, esimp at *, cases pf, esimp,
  apply is_equiv.homotopy_closed (ap f),
  intro p, exact (concat_1p _)^-1
Defined.

Definition is_equiv_apn (n : ℕ) (f : A ->* B) [H : is_equiv f]
  : is_equiv (apn n f).
Proof.
  induction n with n IH,
  { exact H},
  { exact is_equiv_ap1 (apn n f)}
Defined.

Definition pinverse_con {X : pType} (p q : loops X)
  : pinverse (p @ q) = pinverse q @ pinverse p.
  !con_inv

Definition pinverse_inv {X : pType} (p : loops X)
  : pinverse p^-1 = (pinverse p)^-1.
  idp

Definition ap1_pcompose_pinverse {X Y : pType} (f : X ->* Y) :
  Ω-> f o* pinverse ==* pinverse o* Ω-> f.
  Build_pHomotopy (ap1_gen_inv f (point_eq f) (point_eq f))
  abstract begin
  induction Y with Y y₀, induction f with f f₀, esimp at * ⊢, induction f₀, reflexivity
Defined. end

Definition is_equiv_pcast [instance] {A B : pType} (p : A = B) : is_equiv (pcast p).
  !is_equiv_cast

  (* categorical properties of pointed homotopies *)

  variable (k)
  protectedDefinition reflexivity : k ==* k.
  Build_pHomotopy homotopy.rfl (concat_1p _)
  variable {k}
  protectedDefinition (reflexivity _) [refl] : k ==* k.
  reflexivity k

  protectedDefinition phomotopy.symm [symm] (p : k ==* l) : l ==* k.
  Build_pHomotopy p^-1ʰᵗʸ (inv_con_eq_of_eq_con (point_htpy p)^-1)

  protectedDefinition phomotopy.trans [trans] (p : k ==* l) (q : l ==* m) :
  k ==* m.
  Build_pHomotopy (fun a => p a @ q a) ((concat_pp_p _ _ _) @ whisker_left (p (point _)) (point_htpy q) @ point_htpy p)

  infix ` @* `:75 . phomotopy.trans
  postfix `^-1*`:(max+1) . phomotopy.symm

  (* equalities and equivalences relating pointed homotopies *)

Definition phomotopy.rec' [recursor] (B : k ==* l -> Type)
  (H : forall (h : k == l) (p : h (point _) @ point_eq l = point_eq k), B (Build_pHomotopy h p))
  (h : k ==* l) : B h.
Proof.
  induction h with h p,
  refine transport (fun p => B (ppi.mk h p)) _ (H h (con_eq_of_eq_con_inv p)),
  apply to_left_inv !eq_con_inv_equiv_con_eq p
Defined.

Definition phomotopy.eta_expand (p : k ==* l) : k ==* l.
  Build_pHomotopy p (point_htpy p)

Definition is_trunc_ppi [instance] (n : ℕ₋₂) {A : pType} (B : A -> Type) (b₀ : B (point _)) [forall a, is_trunc n (B a)] :
  is_trunc n (ppi B b₀).
  is_trunc_equiv_closed_rev _ !ppi.sigma_char

Definition is_trunc_pmap [instance] (n : ℕ₋₂) (A B : pType) [is_trunc n B] :
  is_trunc n (A ->* B).
  !is_trunc_ppi

Definition is_trunc_ppMap [instance] (n : ℕ₋₂) {A B : pType} [is_trunc n B] :
  is_trunc n (ppMap A B).
  !is_trunc_pmap

Definition phomotopy_path (p : k = l) : k ==* l.
  Build_pHomotopy (ap010 ppi.to_fun p) begin induction p => refine (concat_1p _) end

Definition phomotopy_path_idp (k : ppi P p₀) : phomotopy_path idp = reflexivity k.
  idp

Definition pconcat_eq (p : k ==* l) (q : l = m) : k ==* m.
  p @* phomotopy_path q

Definition eq_pconcat (p : k = l) (q : l ==* m) : k ==* m.
  phomotopy_path p @* q

  infix ` @*p `:75 . pconcat_eq
  infix ` @p* `:75 . eq_pconcat

Definition pr1_phomotopy_eq {p q : k ==* l} (r : p = q) (a : A) : p a = q a.
  ap010 to_homotopy r a

Definition pwhisker_left (h : B ->* C) (p : f ==* g) : h o* f ==* h o* g.
  Build_pHomotopy (fun a => ap h (p a))
  abstract (concat_pp_p _ _ _)^-1 @ whisker_right _ ((ap_pp _ _ _)^-1 @ ap02 _ (point_htpy p)) end

Definition pwhisker_right (h : C ->* A) (p : f ==* g) : f o* h ==* g o* h.
  Build_pHomotopy (fun a => p (h a))
  abstract (concat_pp_p _ _ _)^-1 @ whisker_right _ ((ap_pp _ _ _)_eq_con_ap)^-1 @ (concat_pp_p _ _ _) @
  whisker_left _ (point_htpy p) end

Definition pconcat2 {A B C : pType} {h i : B ->* C} {f g : A ->* B}
  (q : h ==* i) (p : f ==* g) : h o* f ==* i o* g.
  pwhisker_left _ p @* pwhisker_right _ q

  variables (k l)

Definition phomotopy.sigma_char
  : (k ==* l) <~> Σ(p : k == l), p (point _) @ point_eq l = point_eq k.
Proof.
  fapply equiv.MK : intros h,
  { exact ⟨h , point_htpy h⟩ },
  { cases h with h p, exact Build_pHomotopy h p },
  { cases h with h p, exact ap (dpair h) (to_right_inv !eq_con_inv_equiv_con_eq p) },
  { induction h using phomotopy.rec' with h p,
  exact ap (Build_pHomotopy h) (to_right_inv !eq_con_inv_equiv_con_eq p) }
Defined.

Definition ppi_eq_equiv_internal : (k = l) <~> (k ==* l).
  calc (k = l) <~> ppi.sigma_char P p₀ k = ppi.sigma_char P p₀ l
  : eq_equiv_fn_eq (ppi.sigma_char P p₀) k l
  ...  <~> Σ(p : k = l),
  pathover (fun h => h (point _) = p₀) (point_eq k) p (point_eq l)
  : sigma_eq_equiv _ _
  ...  <~> Σ(p : k = l),
  point_eq k = ap (fun h => h (point _)) p @ point_eq l
  : sigma_equiv_sigma_right
  (fun p => eq_pathover_equiv_Fl p (point_eq k) (point_eq l))
  ...  <~> Σ(p : k = l),
  point_eq k = apd10 p (point _) @ point_eq l
  : sigma_equiv_sigma_right
  (fun p => equiv_eq_closed_right _ (whisker_right _ (ap_eq_apd10 p _)))
  ...  <~> Σ(p : k == l), point_eq k = p (point _) @ point_eq l
  : sigma_equiv_sigma_left' eq_equiv_homotopy
  ...  <~> Σ(p : k == l), p (point _) @ point_eq l = point_eq k
  : sigma_equiv_sigma_right (fun p => eq_equiv_eq_symm _ _)
  ...  <~> (k ==* l) : phomotopy.sigma_char k l

Definition ppi_eq_equiv_internal_idp :
  ppi_eq_equiv_internal k k idp = reflexivity k.
Proof.
  apply ap (Build_pHomotopy (homotopy.refl _)), induction k with k k₀,
  esimp at * ⊢, induction k₀, reflexivity
Defined.

Definition ppi_eq_equiv : (k = l) <~> (k ==* l).
Proof.
  refine equiv_change_fun (ppi_eq_equiv_internal k l) _ =>
  { apply phomotopy_path },
  { intro p, induction p, exact ppi_eq_equiv_internal_idp k }
Defined.
  variables {k l}

Definition pmap_eq_equiv (f g : A ->* B) : (f = g) <~> (f ==* g).
  ppi_eq_equiv f g

Definition path_pforall (p : k ==* l) : k = l.
  to_inv (ppi_eq_equiv k l) p

Definition path_pforall_refl (k : ppi P p₀) : path_pforall (reflexivity k) = idpath k.
Proof.
  apply to_inv_eq_of_eq, reflexivity
Defined.

Definition phomotopy_of_homotopy (h : k == l) [forall a, is_set (P a)] : k ==* l.
Proof.
  fapply Build_pHomotopy,
  { exact h },
  { apply is_set.elim }
Defined.

Definition ppi_eq_of_homotopy [forall a, is_set (P a)] (p : k == l) : k = l.
  path_pforall (phomotopy_of_homotopy p)

Definition pmap_eq_of_homotopy [is_set B] (p : f == g) : f = g.
  ppi_eq_of_homotopy p

Definition phomotopy_path_of_phomotopy (p : k ==* l) : phomotopy_path (path_pforall p) = p.
  to_right_inv (ppi_eq_equiv k l) p

Definition phomotopy_rec_eq [recursor] {Q : (k ==* k') -> Type} (p : k ==* k')
  (H : forall (q : k = k'), Q (phomotopy_path q)) : Q p.
  phomotopy_path_of_phomotopy p # H (path_pforall p)

Definition phomotopy_rec_idp [recursor] {Q : forall {k' : ppi P p₀}, (k ==* k') -> Type}
  {k' : ppi P p₀} (H : k ==* k') (q : Q (reflexivity k)) : Q H.
Proof.
  induction H using phomotopy_rec_eq with t,
  induction t, exact phomotopy_path_idp k # q,
Defined.

Definition phomotopy_rec_idp' (Q : forall (k' : ppi P p₀), (k ==* k') -> (k = k') -> Type)
  (q : Q (reflexivity _) idp) (k' : ppi P p₀) (H : k ==* k') : Q H (path_pforall H).
Proof.
  induction H using phomotopy_rec_idp,
  exact transport (Q (reflexivity _)) !path_pforall_refl^-1 q
Defined.

  attribute phomotopy.rec' [recursor]

Definition phomotopy_rec_eq_phomotopy_path {Q : (k ==* l) -> Type} (p : k = l)
  (H : forall (q : k = l), Q (phomotopy_path q)) : phomotopy_rec_eq (phomotopy_path p) H = H p.
Proof.
  unfold phomotopy_rec_eq,
  refine ap (fun p => p # _) !adj @ _,
  refine !tr_compose^-1 @ _,
  apply apdt
Defined.

Definition phomotopy_rec_idp_refl {Q : forall {l}, (k ==* l) -> Type} (H : Q (reflexivity k)) :
  phomotopy_rec_idp (reflexivity _) H = H.
  !phomotopy_rec_eq_phomotopy_path

Definition phomotopy_rec_idp'_refl (Q : forall (k' : ppi P p₀), (k ==* k') -> (k = k') -> Type)
  (q : Q (reflexivity _) idp) :
  phomotopy_rec_idp' Q q (reflexivity _) = transport (Q (reflexivity _)) !path_pforall_refl^-1 q.
  !phomotopy_rec_idp_refl

  (* maps out of or into contractible types *)
Definition phomotopy_of_is_contr_cod (k l : ppi P p₀) [forall a, is_contr (P a)] :
  k ==* l.
  Build_pHomotopy (fun a => !eq_of_is_contr) !eq_of_is_contr

Definition phomotopy_of_is_contr_cod_pmap (f g : A ->* B) [is_contr B] : f ==* g.
  phomotopy_of_is_contr_cod f g

Definition phomotopy_of_is_contr_dom (k l : ppi P p₀) [is_contr A] : k ==* l.
Proof.
  fapply Build_pHomotopy,
  { intro a, exact eq_of_pathover_idp (change_path !is_prop.elim
  (apd k !is_prop.elim @op point_eq k @ (point_eq l)^-1 @o apd l !is_prop.elim)) },
  rewrite [▸*, +is_prop_elim_self, +apd_idp, cono_idpo],
  refine ap (fun x => eq_of_pathover_idp (change_path x _)) !is_prop_elim_self ◾ idp @ _,
  xrewrite [change_path_idp, idpo_concato_eq, inv_con_cancel_right],
Defined.

  (* adjunction between (-)₊ : Type -> pType and pType.carrier : pType -> Type  *)
Definition pmap_equiv_left (A : Type) (B : pType) : A₊ ->* B <~> (A -> B).
Proof.
  fapply equiv.MK,
  { intro f a, cases f with f p, exact f (some a) },
  { intro f, fconstructor,
  intro a, cases a, exact (point _), exact f a,
  reflexivity },
  { intro f, reflexivity },
  { intro f, cases f with f p, esimp, fapply path_pforall, fapply Build_pHomotopy,
  { intro a, cases a; all_goals (esimp at *), exact p^-1 },
  { esimp, exact (con_Vp _) }},
Defined.

  (* pmap_pbool_pequiv is the pointed equivalence *)
Definition pmap_pbool_equiv (B : pType) : (pbool ->* B) <~> B.
Proof.
  fapply equiv.MK,
  { intro f, cases f with f p, exact f tt },
  { intro b, fconstructor,
  intro u, cases u, exact (point _), exact b,
  reflexivity },
  { intro b, reflexivity },
  { intro f, cases f with f p, esimp, fapply path_pforall, fapply Build_pHomotopy,
  { intro a, cases a; all_goals (esimp at *), exact p^-1 },
  { esimp, exact (con_Vp _) }},
Defined.

  (*
  Pointed maps respecting pointed homotopies.
  In general we need function extensionality for pap =>
  but for particular F we can do it without function extensionality.
  This might be preferred, because such pointed homotopies compute. On the other hand,
  when using function extensionality => it's easier to prove that if p is reflexivity, then the
  resulting pointed homotopy is reflexivity
  *)
Definition pap (F : (A ->* B) -> (C ->* D)) {f g : A ->* B} (p : f ==* g) : F f ==* F g.
Proof.
  induction p using phomotopy_rec_idp, reflexivity
Defined.

Definition pap_refl (F : (A ->* B) -> (C ->* D)) (f : A ->* B) :
  pap F (reflexivity f) = reflexivity (F f).
  !phomotopy_rec_idp_refl

Definition ap1_phomotopy {f g : A ->* B} (p : f ==* g) : Ω-> f ==* Ω-> g.
  pap Ω-> p

Definition ap1_phomotopy_refl {X Y : pType} (f : X ->* Y) :
  ap1_phomotopy (reflexivity f) = reflexivity (Ω-> f).
  !pap_refl

  --a proof not using function extensionality:
Definition ap1_phomotopy_explicit {f g : A ->* B} (p : f ==* g) : Ω-> f ==* Ω-> g.
Proof.
  induction p with p q, induction f with f pf, induction g with g pg, induction B with B b,
  esimp at * ⊢, induction q, induction pg,
  fapply Build_pHomotopy,
  { intro l, refine _ @ (concat_1p _)^-1ᵖ, refine (concat_pp_p _ _ _) @ _, apply inv_con_eq_of_eq_con,
  apply ap_con_eq_con_ap},
  { induction A with A a, unfold [ap_con_eq_con_ap], generalize p a, generalize g a, intro b q,
  induction q, reflexivity}
Defined.

Definition apn_phomotopy {f g : A ->* B} (n : ℕ) (p : f ==* g) : apn n f ==* apn n g.
Proof.
  induction n with n IH,
  { exact p},
  { exact ap1_phomotopy IH}
Defined.

  (* the following twoDefinitiongs are mostly the same, maybe we should remove one *)
Definition ap_path_pforall {A B : pType} {f g : A ->* B} (p : f ==* g) (a : A) :
  ap (fun f : A ->* B => f a) (path_pforall p) = p a.
  ap010 to_homotopy (phomotopy_path_of_phomotopy p) a

Definition to_fun_path_pforall {A B : pType} {f g : A ->* B} (p : f ==* g) (a : A) :
  ap010 pmap.to_fun (path_pforall p) a = p a.
Proof.
  induction p using phomotopy_rec_idp,
  exact ap (fun x => ap010 pmap.to_fun x a) !path_pforall_refl
Defined.

Definition ap1_path_pforall {A B : pType} {f g : A ->* B} (p : f ==* g) :
  ap Ω-> (path_pforall p) = path_pforall (ap1_phomotopy p).
Proof.
  induction p using phomotopy_rec_idp,
  refine ap02 _ !path_pforall_refl @ !path_pforall_refl^-1 @ ap path_pforall _,
  exact !ap1_phomotopy_refl^-1
Defined.

  (* pointed homotopies between the given pointed maps *)

Definition ap1_pid {A : pType} : ap1 (pid A) ==* pid (loops A).
Proof.
  fapply Build_pHomotopy,
  { intro p, esimp, refine (concat_1p _) @ !ap_id},
  { reflexivity}
Defined.

Definition ap1_pinverse {A : pType} : ap1 (@pinverse A) ==* @pinverse (loops A).
Proof.
  fapply Build_pHomotopy,
  { intro p, refine (concat_1p _) @ _, exact !inv_eq_inv2^-1 },
  { reflexivity}
Defined.

Definition ap1_gen_compose {A B C : Type} (g : B -> C) (f : A -> B) {a₁ a₂ : A} {b₁ b₂ : B}
  {c₁ c₂ : C} (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (r₁ : g b₁ = c₁) (r₂ : g b₂ = c₂) (p : a₁ = a₂) :
  ap1_gen (g o f) (ap g q₁ @ r₁) (ap g q₂ @ r₂) p = ap1_gen g r₁ r₂ (ap1_gen f q₁ q₂ p).
Proof. induction p, induction q₁, induction q₂, induction r₁, induction r₂, reflexivity end

Definition ap1_gen_compose_idp {A B C : Type} (g : B -> C) (f : A -> B) {a : A}
  {b : B} {c : C} (q : f a = b) (r : g b = c) :
  ap1_gen_compose g f q q r r idp @ (ap (ap1_gen g r r) (ap1_gen_idp f q) @ ap1_gen_idp g r) =
  ap1_gen_idp (g o f) (ap g q @ r).
Proof. induction q, induction r, reflexivity end

Definition ap1_pcompose {A B C : pType} (g : B ->* C) (f : A ->* B) :
  ap1 (g o* f) ==* ap1 g o* ap1 f.
  Build_pHomotopy (ap1_gen_compose g f (point_eq f) (point_eq f) (point_eq g) (point_eq g))
  (ap1_gen_compose_idp g f (point_eq f) (point_eq g))

Definition ap1_pconst (A B : pType) : Ω->(pconst A B) ==* pconst (loops A) (loops B).
  Build_pHomotopy (fun p => ap1_gen_idp_left (const A (point _)) p @ ap_constant p (point _)) rfl

Definition ap1_gen_con_left {A B : Type} {a a' : A} {b₀ b₁ b₂ : B}
  {f : A -> b₀ = b₁} {f' : A -> b₁ = b₂} {q₀ q₁ : b₀ = b₁} {q₀' q₁' : b₁ = b₂}
  (r₀ : f a = q₀) (r₁ : f a' = q₁) (r₀' : f' a = q₀') (r₁' : f' a' = q₁') (p : a = a') :
  ap1_gen (fun a => f a @ f' a) (r₀ ◾ r₀') (r₁ ◾ r₁') p =
  whisker_right q₀' (ap1_gen f r₀ r₁ p) @ whisker_left q₁ (ap1_gen f' r₀' r₁' p).
Proof. induction r₀, induction r₁, induction r₀', induction r₁', induction p, reflexivity end

Definition ap1_gen_con_left_idp {A B : Type} {a : A} {b₀ b₁ b₂ : B}
  {f : A -> b₀ = b₁} {f' : A -> b₁ = b₂} {q₀ : b₀ = b₁} {q₁ : b₁ = b₂}
  (r₀ : f a = q₀) (r₁ : f' a = q₁) :
  ap1_gen_con_left r₀ r₀ r₁ r₁ idp =
  (con_Vp _) @ (ap (whisker_right q₁) (con_Vp _) ◾ ap (whisker_left _) (con_Vp _))^-1.
Proof. induction r₀, induction r₁, reflexivity end

Definition ptransport_change_eq {A : Type} (B : A -> pType) {a a' : A} {p q : a = a'}
  (r : p = q) : ptransport B p ==* ptransport B q.
  Build_pHomotopy (fun b => ap (fun p => transport B p b) r) begin induction r, apply idp_con end

Definition pnatural_square {A B : Type} (X : B -> pType) {f g : A -> B}
  (h : forall a, X (f a) ->* X (g a)) {a a' : A} (p : a = a') :
  h a' o* ptransport X (ap f p) ==* ptransport X (ap g p) o* h a.
  by induction p; exact !pcompose_pid @* !pid_pcompose^-1*

Definition apn_pid {A : pType} (n : ℕ) : apn n (pid A) ==* pid (Ω[n] A).
Proof.
  induction n with n IH,
  { reflexivity},
  { exact ap1_phomotopy IH @* ap1_pid}
Defined.

Definition apn_pconst (A B : pType) (n : ℕ) :
  apn n (pconst A B) ==* pconst (Ω[n] A) (Ω[n] B).
Proof.
  induction n with n IH,
  { reflexivity },
  { exact ap1_phomotopy IH @* !ap1_pconst }
Defined.

Definition apn_pcompose (n : ℕ) (g : B ->* C) (f : A ->* B) :
  apn n (g o* f) ==* apn n g o* apn n f.
Proof.
  induction n with n IH,
  { reflexivity},
  { refine ap1_phomotopy IH @* _, apply ap1_pcompose}
Defined.

Definition pcast_idp {A : pType} : pcast (idpath A) ==* pid A.
  by reflexivity

Definition pinverse_pinverse (A : pType) : pinverse o* pinverse ==* pid (loops A).
Proof.
  fapply Build_pHomotopy,
  { apply inv_inv},
  { reflexivity}
Defined.

Definition pcast_ap_loop {A B : pType} (p : A = B) :
  pcast (ap loops p) ==* ap1 (pcast p).
Proof.
  fapply Build_pHomotopy,
  { intro a, induction p, esimp, exact ((concat_1p _) @ !ap_id)^-1},
  { induction p, reflexivity}
Defined.

Definition ap1_pmap_of_map {A B : Type} (f : A -> B) (a : A) :
  ap1 (pmap_of_map f a) ==* pmap_of_map (ap f) (idpath a).
Proof.
  fapply Build_pHomotopy,
  { intro a, esimp, apply idp_con},
  { reflexivity}
Defined.

Definition pcast_commute {A : Type} {B C : A -> pType} (f : forall a, B a ->* C a)
  {a₁ a₂ : A} (p : a₁ = a₂) : pcast (ap C p) o* f a₁ ==* f a₂ o* pcast (ap B p).
  Build_pHomotopy
Proof. induction p, reflexivity end
Proof. induction p, esimp, refine (concat_1p _) @ (concat_1p _) @ !ap_id^-1 end

  (* pointed equivalences *)

  structure pequiv (A B : pType).
  mk' :: (to_pmap : A ->* B)
  (to_pinv1 : B ->* A)
  (to_pinv2 : B ->* A)
  (pright_inv : to_pmap o* to_pinv1 ==* pid B)
  (pleft_inv : to_pinv2 o* to_pmap ==* pid A)

  infix ` <~>* `:25 . pequiv

Definition pmap_of_pequiv [coercion] {A B : pType} (f : A <~>* B) :
  @ppi A (fun a => B) (point _).
  pequiv.to_pmap f

Definition to_pinv (f : A <~>* B) : B ->* A.
  pequiv.to_pinv1 f

Definition pleft_inv' (f : A <~>* B) : to_pinv f o* f ==* pid A.
  let g . to_pinv f in
  let h . pequiv.to_pinv2 f in
  calc g o* f ==* pid A o* (g o* f)    : by exact !pid_pcompose^-1*
  ... ==* (h o* f) o* (g o* f) : by exact pwhisker_right _ (pequiv.pleft_inv f)^-1*
  ... ==* h o* (f o* g) o* f   : by exact !passoc @* pwhisker_left _ !passoc^-1*
  ... ==* h o* pid B o* f      : by exact !pwhisker_left (!pwhisker_right !pequiv.pright_inv)
  ... ==* h o* f               : by exact pwhisker_left _ !pid_pcompose
  ... ==* pid A                : by exact pequiv.pleft_inv f

Definition equiv_of_pequiv [coercion] (f : A <~>* B) : A <~> B.
  have is_equiv f, from adjointify f (to_pinv f) (pequiv.pright_inv f) (pleft_inv' f),
  equiv.mk f _

  attribute pointed._trans_of_equiv_of_pequiv pointed._trans_of_pmap_of_pequiv [unfold 3]

Definition pequiv.to_is_equiv [instance] (f : A <~>* B) :
  is_equiv (pointed._trans_of_equiv_of_pequiv f).
  adjointify f (to_pinv f) (pequiv.pright_inv f) (pleft_inv' f)

Definition pequiv.to_is_equiv' [instance] (f : A <~>* B) :
  is_equiv (pointed._trans_of_pmap_of_pequiv f).
  pequiv.to_is_equiv f

  protectedDefinition pequiv.MK (f : A ->* B) (g : B ->* A)
  (gf : g o* f ==* !pid) (fg : f o* g ==* !pid) : A <~>* B.
  pequiv.mk' f g g fg gf

Definition pinv (f : A ->* B) (H : is_equiv f) : B ->* A.
  Build_pMap f^-1ᶠ (ap f^-1ᶠ (point_eq f)^-1 @ (left_inv f (point _)))

Definition pequiv_of_pmap (f : A ->* B) (H : is_equiv f) : A <~>* B.
  pequiv.mk' f (pinv f H) (pinv f H)
  abstract begin
  fapply Build_pHomotopy, exact right_inv f,
  induction f with f f₀, induction B with B b₀, esimp at *, induction f₀, esimp,
  exact adj f (point _) @ ap02 f (concat_1p _)^-1
Defined. end
  abstract begin
  fapply Build_pHomotopy, exact left_inv f,
  induction f with f f₀, induction B with B b₀, esimp at *, induction f₀, esimp,
  exact (concat_1p _)^-1 @ (concat_1p _)^-1
Defined. end

Definition pequiv.mk (f : A -> B) (H : is_equiv f) (p : f (point _) = (point _)) : A <~>* B.
  pequiv_of_pmap (Build_pMap f p) H

Definition pequiv_of_equiv (f : A <~> B) (H : f (point _) = (point _)) : A <~>* B.
  pequiv.mk f _ H

  protectedDefinition pequiv.MK' (f : A ->* B) (g : B -> A)
  (gf : forall a, g (f a) = a) (fg : forall b, f (g b) = b) : A <~>* B.
  pequiv.mk f (adjointify f g fg gf) (point_eq f)

  (* reflexivity and symmetry (transitivity is below) *)

  protectedDefinition pequiv.refl [refl] (A : pType) : A <~>* A.
  pequiv.mk' (pid A) (pid A) (pid A) !pid_pcompose !pcompose_pid

  protectedDefinition pequiv.rfl : A <~>* A.
  pequiv.refl A

  protectedDefinition pequiv.symm [symm] (f : A <~>* B) : B <~>* A.
  pequiv.MK (to_pinv f) f (pequiv.pright_inv f) (pleft_inv' f)

  postfix `^-1ᵉ*`:(max + 1) . pequiv.symm

Definition pleft_inv (f : A <~>* B) : f^-1ᵉ* o* f ==* pid A.
  pleft_inv' f

Definition pright_inv (f : A <~>* B) : f o* f^-1ᵉ* ==* pid B.
  pequiv.pright_inv f

Definition to_pmap_pequiv_of_pmap {A B : pType} (f : A ->* B) (H : is_equiv f)
  : pequiv.to_pmap (pequiv_of_pmap f H) = f.
  by reflexivity

Definition to_pmap_pequiv_MK (f : A ->* B) (g : B ->* A)
  (gf : g o* f ==* !pid) (fg : f o* g ==* !pid) : pequiv.MK f g gf fg ==* f.
  by reflexivity

Definition to_pinv_pequiv_MK (f : A ->* B) (g : B ->* A)
  (gf : g o* f ==* !pid) (fg : f o* g ==* !pid) : to_pinv (pequiv.MK f g gf fg) ==* g.
  by reflexivity

  (* more on pointed equivalences *)

Definition pequiv_ap {A : Type} (B : A -> pType) {a a' : A} (p : a = a')
  : B a <~>* B a'.
  pequiv_of_pmap (ptransport B p) !is_equiv_tr

Definition pequiv_change_fun (f : A <~>* B) (f' : A ->* B) (Heq : f == f') : A <~>* B.
  pequiv_of_pmap f' (is_equiv.homotopy_closed f Heq)

Definition pequiv_change_inv (f : A <~>* B) (f' : B ->* A) (Heq : to_pinv f == f')
  : A <~>* B.
  pequiv.MK' f f' (to_left_inv (equiv_change_inv f Heq)) (to_right_inv (equiv_change_inv f Heq))

Definition pequiv_rect' (f : A <~>* B) (P : A -> B -> Type)
  (g : forall b, P (f^-1 b) b) (a : A) : P a (f a).
  left_inv f a # g (f a)

Definition pua {A B : pType} (f : A <~>* B) : A = B.
  pType_eq (equiv_of_pequiv f) !point_eq

Definition pequiv_of_eq {A B : pType} (p : A = B) : A <~>* B.
  pequiv_of_pmap (pcast p) !is_equiv_tr

Definition eq_of_pequiv {A B : pType} (p : A <~>* B) : A = B.
  pType_eq (equiv_of_pequiv p) !point_eq

Definition peap {A B : pType} (F : pType -> pType) (p : A <~>* B) : F A <~>* F B.
  pequiv_of_pmap (pcast (ap F (eq_of_pequiv p))) begin cases eq_of_pequiv p, apply is_equiv_id end

  (* rename pequiv_of_eq_natural *)
Definition pequiv_of_eq_commute {A : Type} {B C : A -> pType} (f : forall a, B a ->* C a)
  {a₁ a₂ : A} (p : a₁ = a₂) : pequiv_of_eq (ap C p) o* f a₁ ==* f a₂ o* pequiv_of_eq (ap B p).
  pcast_commute f p

  (*Definition pequiv.eta_expand {A B : pType} (f : A <~>* B) : A <~>* B . *)
  (* pequiv.mk' f (to_pinv f) (pequiv.to_pinv2 f) (pright_inv f) _ *)

  (*
  theDefinition pequiv_eq, which gives a condition for two pointed equivalences are equal
  is in types.equiv to avoid circular imports
  *)

  (* computation rules of pointed homotopies, possibly combined with pointed equivalences *)
Definition pcancel_left (f : B <~>* C) {g h : A ->* B} (p : f o* g ==* f o* h) : g ==* h.
Proof.
  refine _^-1* @* pwhisker_left f^-1ᵉ* p @* _:
  refine !passoc^-1* @* _:
  refine pwhisker_right _ (pleft_inv f) @* _:
  apply pid_pcompose
Defined.

Definition pcancel_right (f : A <~>* B) {g h : B ->* C} (p : g o* f ==* h o* f) : g ==* h.
Proof.
  refine _^-1* @* pwhisker_right f^-1ᵉ* p @* _:
  refine !passoc @* _:
  refine pwhisker_left _ (pright_inv f) @* _:
  apply pcompose_pid
Defined.

Definition phomotopy_pinv_right_of_phomotopy {f : A <~>* B} {g : B ->* C} {h : A ->* C}
  (p : g o* f ==* h) : g ==* h o* f^-1ᵉ*.
Proof.
  refine _ @* pwhisker_right _ p, symmetry,
  refine !passoc @* _,
  refine pwhisker_left _ (pright_inv f) @* _,
  apply pcompose_pid
Defined.

Definition phomotopy_of_pinv_right_phomotopy {f : B <~>* A} {g : B ->* C} {h : A ->* C}
  (p : g o* f^-1ᵉ* ==* h) : g ==* h o* f.
Proof.
  refine _ @* pwhisker_right _ p, symmetry,
  refine !passoc @* _,
  refine pwhisker_left _ (pleft_inv f) @* _,
  apply pcompose_pid
Defined.

Definition pinv_right_phomotopy_of_phomotopy {f : A <~>* B} {g : B ->* C} {h : A ->* C}
  (p : h ==* g o* f) : h o* f^-1ᵉ* ==* g.
  (phomotopy_pinv_right_of_phomotopy p^-1*)^-1*

Definition phomotopy_of_phomotopy_pinv_right {f : B <~>* A} {g : B ->* C} {h : A ->* C}
  (p : h ==* g o* f^-1ᵉ*) : h o* f ==* g.
  (phomotopy_of_pinv_right_phomotopy p^-1*)^-1*

Definition phomotopy_pinv_left_of_phomotopy {f : B <~>* C} {g : A ->* B} {h : A ->* C}
  (p : f o* g ==* h) : g ==* f^-1ᵉ* o* h.
Proof.
  refine _ @* pwhisker_left _ p, symmetry,
  refine !passoc^-1* @* _,
  refine pwhisker_right _ (pleft_inv f) @* _,
  apply pid_pcompose
Defined.

Definition phomotopy_of_pinv_left_phomotopy {f : C <~>* B} {g : A ->* B} {h : A ->* C}
  (p : f^-1ᵉ* o* g ==* h) : g ==* f o* h.
Proof.
  refine _ @* pwhisker_left _ p, symmetry,
  refine !passoc^-1* @* _,
  refine pwhisker_right _ (pright_inv f) @* _,
  apply pid_pcompose
Defined.

Definition pinv_left_phomotopy_of_phomotopy {f : B <~>* C} {g : A ->* B} {h : A ->* C}
  (p : h ==* f o* g) : f^-1ᵉ* o* h ==* g.
  (phomotopy_pinv_left_of_phomotopy p^-1*)^-1*

Definition phomotopy_of_phomotopy_pinv_left {f : C <~>* B} {g : A ->* B} {h : A ->* C}
  (p : h ==* f^-1ᵉ* o* g) : f o* h ==* g.
  (phomotopy_of_pinv_left_phomotopy p^-1*)^-1*

Definition pcompose2 {A B C : pType} {g g' : B ->* C} {f f' : A ->* B} (q : g ==* g') (p : f ==* f') :
  g o* f ==* g' o* f'.
  pwhisker_right f q @* pwhisker_left g' p

  infixr ` ◾* `:80 . pcompose2

Definition phomotopy_pinv_of_phomotopy_pid {A B : pType} {f : A ->* B} {g : B <~>* A}
  (p : g o* f ==* pid A) : f ==* g^-1ᵉ*.
  phomotopy_pinv_left_of_phomotopy p @* !pcompose_pid

Definition phomotopy_pinv_of_phomotopy_pid' {A B : pType} {f : A ->* B} {g : B <~>* A}
  (p : f o* g ==* pid B) : f ==* g^-1ᵉ*.
  phomotopy_pinv_right_of_phomotopy p @* !pid_pcompose

Definition pinv_phomotopy_of_pid_phomotopy {A B : pType} {f : A ->* B} {g : B <~>* A}
  (p : pid A ==* g o* f) : g^-1ᵉ* ==* f.
  (phomotopy_pinv_of_phomotopy_pid p^-1*)^-1*

Definition pinv_phomotopy_of_pid_phomotopy' {A B : pType} {f : A ->* B} {g : B <~>* A}
  (p : pid B ==* f o* g) : g^-1ᵉ* ==* f.
  (phomotopy_pinv_of_phomotopy_pid' p^-1*)^-1*

Definition pinv_pcompose_cancel_left {A B C : pType} (g : B <~>* C) (f : A ->* B) :
  g^-1ᵉ* o* (g o* f) ==* f.
  !passoc^-1* @* pwhisker_right f !pleft_inv @* !pid_pcompose

Definition pcompose_pinv_cancel_left {A B C : pType} (g : C <~>* B) (f : A ->* B) :
  g o* (g^-1ᵉ* o* f) ==* f.
  !passoc^-1* @* pwhisker_right f !pright_inv @* !pid_pcompose

Definition pinv_pcompose_cancel_right {A B C : pType} (g : B ->* C) (f : B <~>* A) :
  (g o* f^-1ᵉ*) o* f ==* g.
  !passoc @* pwhisker_left g !pleft_inv @* !pcompose_pid

Definition pcompose_pinv_cancel_right {A B C : pType} (g : B ->* C) (f : A <~>* B) :
  (g o* f) o* f^-1ᵉ* ==* g.
  !passoc @* pwhisker_left g !pright_inv @* !pcompose_pid

Definition pinv_pinv {A B : pType} (f : A <~>* B) : (f^-1ᵉ*)^-1ᵉ* ==* f.
  (phomotopy_pinv_of_phomotopy_pid (pleft_inv f))^-1*

Definition pinv2 {A B : pType} {f f' : A <~>* B} (p : f ==* f') : f^-1ᵉ* ==* f'^-1ᵉ*.
  phomotopy_pinv_of_phomotopy_pid (pinv_right_phomotopy_of_phomotopy (!pid_pcompose @* p)^-1*)

  postfix [parsing_only] `⁻²*`:(max+10) . pinv2

  protectedDefinition pequiv.trans [trans] (f : A <~>* B) (g : B <~>* C) : A <~>* C.
  pequiv.MK (g o* f) (f^-1ᵉ* o* g^-1ᵉ*)
  abstract !passoc @* pwhisker_left _ (pinv_pcompose_cancel_left g f) @* pleft_inv f end
  abstract !passoc @* pwhisker_left _ (pcompose_pinv_cancel_left f g^-1ᵉ*) @* pright_inv g end

Definition pequiv_compose {A B C : pType} (g : B <~>* C) (f : A <~>* B) : A <~>* C.
  pequiv.trans f g

  infix ` @e* `:75 . pequiv.trans
  infixr ` o*ᵉ `:60 . pequiv_compose

Definition to_pmap_pequiv_trans {A B C : pType} (f : A <~>* B) (g : B <~>* C)
  : pequiv.to_pmap (f @e* g) = g o* f.
  by reflexivity

Definition to_fun_pequiv_trans {X Y Z : pType} (f : X <~>* Y) (g :Y <~>* Z) : f @e* g == g o f.
  fun x => idp

Definition peconcat_eq {A B C : pType} (p : A <~>* B) (q : B = C) : A <~>* C.
  p @e* pequiv_of_eq q

Definition eq_peconcat {A B C : pType} (p : A = B) (q : B <~>* C) : A <~>* C.
  pequiv_of_eq p @e* q


  infix ` @e*p `:75 . peconcat_eq
  infix ` @pe* `:75 . eq_peconcat


Definition trans_pinv {A B C : pType} (f : A <~>* B) (g : B <~>* C) :
  (f @e* g)^-1ᵉ* ==* f^-1ᵉ* o* g^-1ᵉ*.
  by reflexivity

Definition pinv_trans_pinv_left {A B C : pType} (f : B <~>* A) (g : B <~>* C) :
  (f^-1ᵉ* @e* g)^-1ᵉ* ==* f o* g^-1ᵉ*.
  by reflexivity

Definition pinv_trans_pinv_right {A B C : pType} (f : A <~>* B) (g : C <~>* B) :
  (f @e* g^-1ᵉ*)^-1ᵉ* ==* f^-1ᵉ* o* g.
  by reflexivity

Definition pinv_trans_pinv_pinv {A B C : pType} (f : B <~>* A) (g : C <~>* B) :
  (f^-1ᵉ* @e* g^-1ᵉ*)^-1ᵉ* ==* f o* g.
  by reflexivity

  (* pointed equivalences between particular pointed types *)

  (* TODO: remove is_equiv_apn, which is proven again here *)
Definition loopn_pequiv_loopn (n : ℕ) (f : A <~>* B) : Ω[n] A <~>* Ω[n] B.
  pequiv.MK (apn n f) (apn n f^-1ᵉ*)
  abstract begin
  induction n with n IH,
  { apply pleft_inv},
  { replace nat.succ n with n + 1,
  rewrite [+apn_succ],
  refine !ap1_pcompose^-1* @* _,
  refine ap1_phomotopy IH @* _,
  apply ap1_pid}
Defined. end
  abstract begin
  induction n with n IH,
  { apply pright_inv},
  { replace nat.succ n with n + 1,
  rewrite [+apn_succ],
  refine !ap1_pcompose^-1* @* _,
  refine ap1_phomotopy IH @* _,
  apply ap1_pid}
Defined. end

Definition loop_pequiv_loop (f : A <~>* B) : loops A <~>* loops B.
  loopn_pequiv_loopn 1 f

Definition loop_pequiv_eq_closed {A : Type} {a a' : A} (p : a = a')
  : pointed.MK (a = a) idp <~>* pointed.MK (a' = a') idp.
  pequiv_of_equiv (loop_equiv_eq_closed p) (con.left_inv p)

Definition to_pmap_loopn_pequiv_loopn (n : ℕ) (f : A <~>* B)
  : loopn_pequiv_loopn n f ==* apn n f.
  by reflexivity

Definition to_pinv_loopn_pequiv_loopn (n : ℕ) (f : A <~>* B)
  : (loopn_pequiv_loopn n f)^-1ᵉ* ==* apn n f^-1ᵉ*.
  by reflexivity

Definition loopn_pequiv_loopn_con (n : ℕ) (f : A <~>* B) (p q : Ω[n+1] A)
  : loopn_pequiv_loopn (n+1) f (p @ q) =
  loopn_pequiv_loopn (n+1) f p @ loopn_pequiv_loopn (n+1) f q.
  ap1_con (loopn_pequiv_loopn n f) p q

Definition loop_pequiv_loop_con {A B : pType} (f : A <~>* B) (p q : loops A)
  : loop_pequiv_loop f (p @ q) = loop_pequiv_loop f p @ loop_pequiv_loop f q.
  loopn_pequiv_loopn_con 0 f p q

Definition loopn_pequiv_loopn_rfl (n : ℕ) (A : pType) :
  loopn_pequiv_loopn n (pequiv.refl A) ==* pequiv.refl (Ω[n] A).
Proof.
  exact !to_pmap_loopn_pequiv_loopn @* apn_pid n,
Defined.

Definition loop_pequiv_loop_rfl (A : pType) :
  loop_pequiv_loop (pequiv.refl A) ==* pequiv.refl (loops A).
  loopn_pequiv_loopn_rfl 1 A

Definition apn_pinv (n : ℕ) {A B : pType} (f : A <~>* B) :
  Ω->[n] f^-1ᵉ* ==* (loopn_pequiv_loopn n f)^-1ᵉ*.
  by reflexivity

Definition pmap_functor {A A' B B' : pType} (f : A' ->* A) (g : B ->* B') :
  ppMap A B ->* ppMap A' B'.
  Build_pMap (fun h => g o* h o* f)
  abstract begin
  fapply path_pforall, fapply Build_pHomotopy,
  { esimp, intro a, exact point_eq g},
  { rewrite [▸*, ap_constant], exact (concat_1p _)^-1 }
Defined. end

Definition pequiv_pinverse (A : pType) : loops A <~>* loops A.
  pequiv_of_pmap pinverse !is_equiv_eq_inverse

Definition pequiv_of_eq_pt {A : Type} {a a' : A} (p : a = a') :
  pointed.MK A a <~>* pointed.MK A a'.
  pequiv_of_pmap (pmap_of_eq_pt p) !is_equiv_id

Definition pointed_eta_pequiv (A : pType) : A <~>* pointed.MK A (point _).
  pequiv.mk id !is_equiv_id idp

  (* every pointed map is homotopic to one of the form `pmap_of_map _ _`, up to some
  pointed equivalences *)
Definition phomotopy_pmap_of_map {A B : pType} (f : A ->* B) :
  (pointed_eta_pequiv B @e* (pequiv_of_eq_pt (point_eq f))^-1ᵉ*) o* f o*
  (pointed_eta_pequiv A)^-1ᵉ* ==* pmap_of_map f (point _).
Proof.
  fapply Build_pHomotopy,
  { reflexivity},
  { symmetry, exact (!ap_id @ (concat_1p _)) ◾ ((concat_1p _) @ !ap_id) @ (con_pV _) }
Defined.

  (* properties of iterated loop space *)
  variable (A)
Definition loopn_succ_in (n : ℕ) : Ω[succ n] A <~>* Ω[n] (loops A).
Proof.
  induction n with n IH,
  { reflexivity},
  { exact loop_pequiv_loop IH}
Defined.

Definition loopn_add (n m : ℕ) : Ω[n] (Ω[m] A) <~>* Ω[m+n] (A).
Proof.
  induction n with n IH,
  { reflexivity},
  { exact loop_pequiv_loop IH}
Defined.

Definition loopn_succ_out (n : ℕ) : Ω[succ n] A <~>* Ω(Ω[n] A) .
  by reflexivity

  variable {A}

Definition loopn_succ_in_con {n : ℕ} (p q : Ω[succ (succ n)] A) :
  loopn_succ_in A (succ n) (p @ q) =
  loopn_succ_in A (succ n) p @ loopn_succ_in A (succ n) q.
  !loop_pequiv_loop_con

Definition loopn_loop_irrel (p : point A = point A) : Ω(pointed.Mk p) = Ω[2] A.
Proof.
  intros, fapply pType_eq,
  { esimp, transitivity _,
  apply eq_equiv_fn_eq_of_equiv (equiv_eq_closed_right _ p^-1),
  esimp, apply eq_equiv_eq_closed, apply con.right_inv, apply con.right_inv},
  { esimp, apply con.left_inv}
Defined.

Definition loopn_space_loop_irrel (n : ℕ) (p : point A = point A)
  : Ω[succ n](pointed.Mk p) = Ω[succ (succ n)] A :> pType.
  calc
  Ω[succ n](pointed.Mk p) = Ω[n](loops (pointed.Mk p)) : eq_of_pequiv !loopn_succ_in
  ... = Ω[n] (Ω[2] A)                            : loopn_loop_irrel
  ... = Ω[2+n] A                                 : eq_of_pequiv !loopn_add
  ... = Ω[n+2] A                                 : by rewrite [algebra.add.comm]

Definition apn_succ_phomotopy_in (n : ℕ) (f : A ->* B) :
  loopn_succ_in B n o* Ω->[n + 1] f ==* Ω->[n] (Ω-> f) o* loopn_succ_in A n.
Proof.
  induction n with n IH,
  { reflexivity},
  { exact !ap1_pcompose^-1* @* ap1_phomotopy IH @* !ap1_pcompose}
Defined.

Definition loopn_succ_in_natural {A B : pType} (n : ℕ) (f : A ->* B) :
  loopn_succ_in B n o* Ω->[n+1] f ==* Ω->[n] (Ω-> f) o* loopn_succ_in A n.
  !apn_succ_phomotopy_in

Definition loopn_succ_in_inv_natural {A B : pType} (n : ℕ) (f : A ->* B) :
  Ω->[n + 1] f o* (loopn_succ_in A n)^-1ᵉ* ==* (loopn_succ_in B n)^-1ᵉ* o* Ω->[n] (Ω-> f).
Proof.
  apply pinv_right_phomotopy_of_phomotopy,
  refine _ @* !passoc^-1*,
  apply phomotopy_pinv_left_of_phomotopy,
  apply apn_succ_phomotopy_in
Defined.

Defined. pointed
