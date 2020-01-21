(* Graded (left-) R-modules for a ring R. *)

(* Author: Floris van Doorn *)

import .left_module .direct_sum .submodule --..heq

open is_trunc algebra eq left_module pointed function equiv is_equiv prod group sigma sigma.ops nat
  trunc_index property
namespace left_module

Definition graded (str : Type) (I : Type) : Type . I -> str
Definition graded_module (R : Ring) : Type -> Type . graded (LeftModule R)

(* TODO: We can (probably) make I a type everywhere *)
variables {R : Ring} {I : AddGroup} {M M₁ M₂ M₃ : graded_module R I}

(*
  morphisms between graded modules.
  TheDefinition is unconventional in two ways:
  (1) The degree is determined by an endofunction instead of a element of I => which is equal to adding
  i on the right. This is more flexible. For example, the
  composition of two graded module homomorphisms φ₂ and φ₁ with degrees i₂ and i₁ has type
  M₁ i -> M₂ ((i + i₁) + i₂).
  However, a homomorphism with degree i₁ + i₂ must have type
  M₁ i -> M₂ (i + (i₁ + i₂)),
  which means that we need to insert a transport. With endofunctions this is not a problem:
  fun i => (i + i₁) + i₂
  is a perfectly fine degree of a map
  (2) Since we cannot eliminate all possible transports, we don't define a homomorphism as function
  M₁ i ->lm M₂ (i + deg f)  or  M₁ i ->lm M₂ (deg f i)
  but as a function taking a path as argument. Specifically => for every path
  deg f i = j
  we get a function M₁ i -> M₂ j.
*)

Definition graded_hom_of_deg (d : I <~> I) (M₁ M₂ : graded_module R I) : Type.
forall (i j : I) (p : d i = j), M₁ i ->lm M₂ j

Definition gmd_constant (d : I <~> I) (M₁ M₂ : graded_module R I) : graded_hom_of_deg d M₁ M₂.
fun i j p => lm_constant (M₁ i) (M₂ j)

Definition gmd0 {d : I <~> I} {M₁ M₂ : graded_module R I} : graded_hom_of_deg d M₁ M₂.
gmd_constant d M₁ M₂

structure graded_hom (M₁ M₂ : graded_module R I) : Type.
mk' ::  (d : I <~> I)
  (deg_eq : forall (i : I), d i = i + d 0)
  (fn' : graded_hom_of_deg d M₁ M₂)


Definition deg_eq_id (i : I) : erfl i = i + erfl 0.
!add_zero^-1

Definition deg_eq_inv {d : I <~> I} (pd : forall (i : I), d i = i + d 0) (i : I) : d^-1ᵉ i = i + d^-1ᵉ 0.
inv_eq_of_eq (!pd @ !neg_add_cancel_right)^-1 @
ap (fun x => i + x) ((to_left_inv d _)^-1 @ ap d^-1ᵉ (!pd @ add.left_inv (d 0)))

Definition deg_eq_con {d₁ d₂ : I <~> I} (pd₁ : forall (i : I), d₁ i = i + d₁ 0) (pd₂ : forall (i : I), d₂ i = i + d₂ 0)
  (i : I) : (d₁ @e d₂) i = i + (d₁ @e d₂) 0.
ap d₂ !pd₁ @ !pd₂ @ !add.assoc @ ap (fun x => i + x) !pd₂^-1

notation M₁ ` ->gm ` M₂ . graded_hom M₁ M₂

abbreviation deg . @graded_hom.d
abbreviation deg_eq . @graded_hom.deg_eq
postfix ` ↘`:max . graded_hom.fn' (* there is probably a better character for this? Maybe ↷? *)

Definition graded_hom_fn [coercion] (f : M₁ ->gm M₂) (i : I) : M₁ i ->lm M₂ (deg f i).
f ↘ idp

Definition graded_hom_fn_out (f : M₁ ->gm M₂) (i : I) : M₁ ((deg f)^-1ᵉ i) ->lm M₂ i.
f ↘ (to_right_inv (deg f) i)

infix ` ← `:max . graded_hom_fn_out (* todo: change notation *)

(*Definition graded_hom_fn_out_rec (f : M₁ ->gm M₂) *)
(*   (P : forall {i j} (p : deg f i = j) (m : M₁ i) (n : M₂ j), Type) *)
(*   (H : forall i m, P (right_inv (deg f) i) m (f ← i m)) {i j : I} *)
(*   (p : deg f i = j) (m : M₁ i) (n : M₂ j) : P p m (f ↘ p m) . *)
(* begin *)
(*   revert i j p m n, refine equiv_rect (deg f)^-1ᵉ _ _, intro i, *)
(*   refine eq.rec_to (right_inv (deg f) i) _, *)
(*   intro m n, exact H i m *)
(* end *)

(*Definition graded_hom_fn_rec (f : M₁ ->gm M₂) *)
(*   {P : forall {i j} (p : deg f i = j) (m : M₁ i) (n : M₂ j), Type} *)
(*   (H : forall i m, P idp m (f i m)) (i j : I) *)
(*   (p : deg f i = j) (m : M₁ i) : P p m (f ↘ p m) . *)
(* begin *)
(*   induction p, apply H *)
(* end *)

(*Definition graded_hom_fn_out_rec (f : M₁ ->gm M₂) *)
(*   {P : forall {i j} (p : deg f i = j) (m : M₁ i) (n : M₂ j), Type} *)
(*   (H : forall i m, P idp m (f i m)) (i : I) (m : M₁ ((deg f)^-1ᵉ i)) : *)
(*   P (right_inv (deg f) i) m (f ← i m) . *)
(* graded_hom_fn_rec f H (right_inv (deg f) i) m *)

(*Definition graded_hom_fn_out_rec_simple (f : M₁ ->gm M₂) *)
(*   {P : forall {j} (n : M₂ j), Type} *)
(*   (H : forall i m, P (f i m)) (i : I) (m : M₁ ((deg f)^-1ᵉ i)) : *)
(*   P (f ← i m) . *)
(* graded_hom_fn_out_rec f H m *)

Definition graded_hom.mk (d : I <~> I) (pd : forall (i : I), d i = i + d 0)
  (fn : forall i, M₁ i ->lm M₂ (d i)) : M₁ ->gm M₂.
graded_hom.mk' d pd (fun i j p => homomorphism_of_eq (ap M₂ p) olm fn i)

Definition graded_hom.mk_out (d : I <~> I) (pd : forall (i : I), d i = i + d 0)
  (fn : forall i, M₁ (d^-1 i) ->lm M₂ i) : M₁ ->gm M₂.
graded_hom.mk' d pd (fun i j p => fn j olm homomorphism_of_eq (ap M₁ (eq_inv_of_eq p)))

Definition graded_hom.mk_out' (d : I <~> I) (pd : forall (i : I), d i = i + d 0)
  (fn : forall i, M₁ (d i) ->lm M₂ i) : M₁ ->gm M₂.
graded_hom.mk' d^-1ᵉ (deg_eq_inv pd) (fun i j p => fn j olm homomorphism_of_eq (ap M₁ (eq_inv_of_eq p)))

Definition graded_hom.mk_out_in (d₁ d₂ : I <~> I)
  (pd₁ : forall (i : I), d₁ i = i + d₁ 0) (pd₂ : forall (i : I), d₂ i = i + d₂ 0)
  (fn : forall i, M₁ (d₁ i) ->lm M₂ (d₂ i)) : M₁ ->gm M₂.
graded_hom.mk' (d₁^-1ᵉ @e d₂) (deg_eq_con (deg_eq_inv pd₁) pd₂)
  (fun i j p => homomorphism_of_eq (ap M₂ p) olm fn (d₁^-1ᵉ i) olm homomorphism_of_eq (ap M₁ (to_right_inv d₁ i)^-1))

Definition graded_hom_eq_transport (f : M₁ ->gm M₂) {i j : I} (p : deg f i = j) (m : M₁ i) :
  f ↘ p m = transport M₂ p (f i m).
by induction p; reflexivity

Definition graded_hom_mk_refl (d : I <~> I) (pd : forall (i : I), d i = i + d 0)
  (fn : forall i, M₁ i ->lm M₂ (d i)) {i : I} (m : M₁ i) : graded_hom.mk d pd fn i m = fn i m.
by reflexivity

lemma graded_hom_mk_out'_destruct (d : I <~> I) (pd : forall (i : I), d i = i + d 0)
  (fn : forall i, M₁ (d i) ->lm M₂ i) {i : I} (m : M₁ (d i)) :
  graded_hom.mk_out' d pd fn ↘ (left_inv d i) m = fn i m.
Proof.
  unfold [graded_hom.mk_out'],
  apply ap (fun x => fn i (cast x m)),
  refine !ap_compose^-1 @ ap02 _ _,
  apply is_set.elim --note: we can also prove this if I is not a set
Defined.

lemma graded_hom_mk_out_destruct (d : I <~> I) (pd : forall (i : I), d i = i + d 0)
  (fn : forall i, M₁ (d^-1 i) ->lm M₂ i) {i : I} (m : M₁ (d^-1 i)) :
  graded_hom.mk_out d pd fn ↘ (right_inv d i) m = fn i m.
Proof.
  rexact graded_hom_mk_out'_destruct d^-1ᵉ (deg_eq_inv pd) fn m
Defined.

lemma graded_hom_mk_out_in_destruct (d₁ : I <~> I) (d₂ : I <~> I)
  (pd₁ : forall (i : I), d₁ i = i + d₁ 0) (pd₂ : forall (i : I), d₂ i = i + d₂ 0)
  (fn : forall i, M₁ (d₁ i) ->lm M₂ (d₂ i)) {i : I} (m : M₁ (d₁ i)) :
  graded_hom.mk_out_in d₁ d₂ pd₁ pd₂ fn ↘ (ap d₂ (left_inv d₁ i)) m = fn i m.
Proof.
  unfold [graded_hom.mk_out_in],
  rewrite [adj d₁, -ap_inv, - +ap_compose, ],
  refine cast_fn_cast_square fn _ _ (con_Vp _) m
Defined.

Definition graded_hom_square (f : M₁ ->gm M₂) {i₁ i₂ j₁ j₂ : I} (p : deg f i₁ = j₁) (q : deg f i₂ = j₂)
  (r : i₁ = i₂) (s : j₁ = j₂) :
  hsquare (f ↘ p) (f ↘ q) (homomorphism_of_eq (ap M₁ r)) (homomorphism_of_eq (ap M₂ s)).
Proof.
  induction p, induction q, induction r,
  have rfl = s, from !is_set.elim, induction this,
  exact homotopy.rfl
Defined.

variable (I) (* for some reason Lean needs to know what I is when applying this lemma *)
Definition graded_hom_eq_zero {f : M₁ ->gm M₂} {i j k : I} {q : deg f i = j} {p : deg f i = k}
  (m : M₁ i) (r : f ↘ q m = 0) : f ↘ p m = 0.
have f ↘ p m = transport M₂ (q^-1 @ p) (f ↘ q m), begin induction p, induction q, reflexivity end,
this @ ap (transport M₂ (q^-1 @ p)) r @ tr_eq_of_pathover (apd (fun i => 0) (q^-1 @ p))

variable {I}

Definition graded_hom_change_image {f : M₁ ->gm M₂} {i j k : I} {m : M₂ k} (p : deg f i = k)
  (q : deg f j = k) (h : image (f ↘ p) m) : image (f ↘ q) m.
Proof.
  have Σ(r : i = j), ap (deg f) r = p @ q^-1,
  from ⟨inj (deg f) (p @ q^-1), !ap_inj'⟩,
  induction this with r s, induction r, induction q, esimp at s, induction s, exact h
Defined.

Definition graded_hom_codom_rec {f : M₁ ->gm M₂} {j : I} {P : forall (i), deg f i = j -> Type}
  {i i' : I} (p : deg f i = j) (h : P p) (q : deg f i' = j) : P q.
Proof.
  have Σ(r : i = i'), ap (deg f) r = p @ q^-1,
  from ⟨inj (deg f) (p @ q^-1), !ap_inj'⟩,
  induction this with r s, induction r, induction q, esimp at s, induction s, exact h
Defined.

variables {f' : M₂ ->gm M₃} {f g h : M₁ ->gm M₂}

Definition graded_hom_compose (f' : M₂ ->gm M₃) (f : M₁ ->gm M₂) : M₁ ->gm M₃.
graded_hom.mk' (deg f @e deg f') (deg_eq_con (deg_eq f) (deg_eq f')) (fun i j p => f' ↘ p olm f i)

infixr ` ogm `:75 . graded_hom_compose

Definition graded_hom_compose_fn (f' : M₂ ->gm M₃) (f : M₁ ->gm M₂) (i : I) (m : M₁ i) :
  (f' ogm f) i m = f' (deg f i) (f i m).
by reflexivity

Definition graded_hom_compose_fn_ext (f' : M₂ ->gm M₃) (f : M₁ ->gm M₂) (i j k : I)
  (p : deg f i = j) (q : deg f' j = k) (r : (deg f @e deg f') i = k) (s : ap (deg f') p @ q = r)
  (m : M₁ i) : ((f' ogm f) ↘ r) m = (f' ↘ q) (f ↘ p m).
by induction s; induction q; induction p; reflexivity

Definition graded_hom_compose_fn_out (f' : M₂ ->gm M₃) (f : M₁ ->gm M₂) (i : I)
  (m : M₁ ((deg f @e deg f')^-1ᵉ i)) : (f' ogm f) ← i m = f' ← i (f ← ((deg f')^-1ᵉ i) m).
graded_hom_compose_fn_ext f' f _ _ _ idp m

(* the following composition might be useful if you want tight control over the paths to which f and f' are applied *)
Definition graded_hom_compose_ext (f' : M₂ ->gm M₃) (f : M₁ ->gm M₂)
  (d : forall (i j) (p : (deg f @e deg f') i = j), I)
  (pf  : forall (i j) (p : (deg f @e deg f') i = j), deg f i = d p)
  (pf' : forall (i j) (p : (deg f @e deg f') i = j), deg f' (d p) = j) : M₁ ->gm M₃.
graded_hom.mk' (deg f @e deg f') (deg_eq_con (deg_eq f) (deg_eq f')) (fun i j p => (f' ↘ (pf' p)) olm (f ↘ (pf p)))

variable (M)
Definition graded_hom_id [refl] : M ->gm M.
graded_hom.mk erfl deg_eq_id (fun i => lmid)
variable {M}
abbreviation gmid . graded_hom_id M

(* reindexing a graded morphism along a group homomorphism.
  We could also reindex along an affine transformation, but don't prove that here
*)
Definition graded_hom_reindex {J : AddGroup} (e : J <~>g I) (f : M₁ ->gm M₂) :
  (fun y => M₁ (e y)) ->gm (fun y => M₂ (e y)).
graded_hom.mk' (group.equiv_of_isomorphism e @e deg f @e (group.equiv_of_isomorphism e)^-1ᵉ)
Proof. intro i, exact ap e^-1ᵍ (deg_eq f (e i)) @ respect_add e^-1ᵍ _ _ @
  ap011 add (to_left_inv (group.equiv_of_isomorphism e) i)
  (ap (e^-1ᵍ o deg f) (respect_zero e)^-1) end
  (fun y₁ y₂ p => f ↘ (to_eq_of_inv_eq (group.equiv_of_isomorphism e) p))

Definition gm_constant (M₁ M₂ : graded_module R I) (d : I <~> I) (pd : forall (i : I), d i = i + d 0)
  (pd : forall (i : I), d i = i + d 0) : M₁ ->gm M₂.
graded_hom.mk' d pd (gmd_constant d M₁ M₂)

Definition is_surjective_graded_hom_compose (x z)
  (f' : M₂ ->gm M₃) (f : M₁ ->gm M₂) (p : deg f' (deg f x) = z)
  (H' : forall (y) (q : deg f' y = z), is_surjective (f' ↘ q))
  (H : forall (y) (q : deg f x = y), is_surjective (f ↘ q)) : is_surjective ((f' ogm f) ↘ p).
Proof.
  induction p,
  apply is_surjective_compose (f' (deg f x)) (f x),
  apply H', apply H
Defined.

structure graded_iso (M₁ M₂ : graded_module R I) : Type.
mk' :: (to_hom : M₁ ->gm M₂)
  (is_equiv_to_hom : forall (i j) (p : deg to_hom i = j), is_equiv (to_hom ↘ p))

infix ` <~>gm `:25 . graded_iso



Definition is_equiv_graded_iso [instance] [priority 1010] (φ : M₁ <~>gm M₂) (i : I) :
  is_equiv (φ i).
graded_iso.is_equiv_to_hom φ idp

Definition isomorphism_of_graded_iso' (φ : M₁ <~>gm M₂) {i j : I} (p : deg φ i = j) :
  M₁ i <~>lm M₂ j.
isomorphism.mk (φ ↘ p) !graded_iso.is_equiv_to_hom

Definition isomorphism_of_graded_iso (φ : M₁ <~>gm M₂) (i : I) :
  M₁ i <~>lm M₂ (deg φ i).
isomorphism.mk (φ i) _

Definition isomorphism_of_graded_iso_out (φ : M₁ <~>gm M₂) (i : I) :
  M₁ ((deg φ)^-1ᵉ i) <~>lm M₂ i.
isomorphism_of_graded_iso' φ (to_right_inv (deg φ) i)

protectedDefinition graded_iso.mk (d : I <~> I)  (pd : forall (i : I), d i = i + d 0)
  (φ : forall i, M₁ i <~>lm M₂ (d i)) : M₁ <~>gm M₂.
Proof.
  apply graded_iso.mk' (graded_hom.mk d pd φ),
  intro i j p, induction p,
  exact to_is_equiv (equiv_of_isomorphism (φ i)),
Defined.

protectedDefinition graded_iso.mk_out (d : I <~> I)
  (pd : forall (i : I), d i = i + d 0) (φ : forall i, M₁ (d^-1 i) <~>lm M₂ i) :
  M₁ <~>gm M₂.
Proof.
  apply graded_iso.mk' (graded_hom.mk_out d pd φ),
  intro i j p, esimp,
  exact @is_equiv_compose _ _ _ _ _ !is_equiv_cast _,
Defined.

Definition graded_iso_of_eq {M₁ M₂ : graded_module R I} (p : M₁ == M₂)
  : M₁ <~>gm M₂.
graded_iso.mk erfl deg_eq_id (fun i => isomorphism_of_eq (p i))

(*Definition to_gminv (φ : M₁ <~>gm M₂) : M₂ ->gm M₁ . *)
(* graded_hom.mk_out (deg φ)^-1ᵉ *)
(*   abstract begin *)
(*     intro i, apply isomorphism.to_hom, symmetry, *)
(*     apply isomorphism_of_graded_iso φ *)
(*   end end *)

variable (M)
Definition graded_iso.refl [refl] : M <~>gm M.
graded_iso.mk equiv.rfl deg_eq_id (fun i => isomorphism.rfl)
variable {M}

Definition graded_iso.rfl [refl] : M <~>gm M . graded_iso.refl M

Definition graded_iso.symm [symm] (φ : M₁ <~>gm M₂) : M₂ <~>gm M₁.
graded_iso.mk_out (deg φ)^-1ᵉ (deg_eq_inv (deg_eq φ)) (fun i => (isomorphism_of_graded_iso φ i)^-1ˡᵐ)

Definition graded_iso.trans [trans] (φ : M₁ <~>gm M₂) (ψ : M₂ <~>gm M₃) : M₁ <~>gm M₃.
graded_iso.mk (deg φ @e deg ψ) (deg_eq_con (deg_eq φ) (deg_eq ψ))
  (fun i => isomorphism_of_graded_iso φ i @lm isomorphism_of_graded_iso ψ (deg φ i))

Definition graded_iso.eq_trans [trans]
  {M₁ M₂ M₃ : graded_module R I} (φ : M₁ == M₂) (ψ : M₂ <~>gm M₃) : M₁ <~>gm M₃.
proof graded_iso.trans (graded_iso_of_eq φ) ψ qed

Definition graded_iso.trans_eq [trans]
  {M₁ M₂ M₃ : graded_module R I} (φ : M₁ <~>gm M₂) (ψ : M₂ == M₃) : M₁ <~>gm M₃.
graded_iso.trans φ (graded_iso_of_eq ψ)

postfix `^-1ᵉᵍᵐ`:(max + 1) . graded_iso.symm
infixl ` @egm `:75 . graded_iso.trans
infixl ` @egmp `:75 . graded_iso.trans_eq
infixl ` @epgm `:75 . graded_iso.eq_trans

Definition graded_hom_of_eq {M₁ M₂ : graded_module R I} (p : M₁ == M₂) : M₁ ->gm M₂.
proof graded_iso_of_eq p qed

Definition fooff {I : Set} (P : I -> Type) {i j : I} (M : P i) (N : P j) . unit
notation M ` ==[`:50 P:0 `] `:0 N:50 . fooff P M N

Definition graded_homotopy (f g : M₁ ->gm M₂) : Type.
forall (i j k) (p : deg f i = j) (q : deg g i = k) (m : M₁ i), f ↘ p m ==[fun (i : Set_of_AddGroup I) => M₂ i] g ↘ q m
(* mk' :: (hd : deg f == deg g) *)
(*        (hfn : forall (i j : I) (pf : deg f i = j) (pg : deg g i = j), f ↘ pf == g ↘ pg) *)

infix ` ~gm `:50 . graded_homotopy

(*Definition graded_homotopy.mk2 (hd : deg f == deg g) (hfn : forall i m, f i m =[hd i] g i m) : f ~gm g . *)
(* graded_homotopy.mk' hd *)
(*   begin *)
(*     intro i j pf pg m, induction (is_set.elim (hd i @ pg) pf), induction pg, esimp, *)
(*     exact graded_hom_eq_transport f (hd i) m @ tr_eq_of_pathover (hfn i m), *)
(*   end *)

Definition graded_homotopy.mk (h : forall i m, f i m ==[fun (i : Set_of_AddGroup I) => M₂ i] g i m) : f ~gm g.
Proof.
  intros i j k p q m, induction q, induction p, constructor --exact h i m
Defined.

(*Definition graded_hom_compose_out {d₁ d₂ : I <~> I} (f₂ : forall i, M₂ i ->lm M₃ (d₂ i)) *)
(*   (f₁ : forall i, M₁ (d₁^-1 i) ->lm M₂ i) : graded_hom.mk d₂ f₂ ogm graded_hom.mk_out d₁ f₁ ~gm *)
(*   graded_hom.mk_out_in d₁^-1ᵉ d₂ _ . *)
(* _ *)

(*Definition graded_hom_out_in_compose_out {d₁ d₂ d₃ : I <~> I} (f₂ : forall i, M₂ (d₂ i) ->lm M₃ (d₃ i)) *)
(*   (f₁ : forall i, M₁ (d₁^-1 i) ->lm M₂ i) : graded_hom.mk_out_in d₂ d₃ f₂ ogm graded_hom.mk_out d₁ f₁ ~gm *)
(*   graded_hom.mk_out_in (d₂ @e d₁^-1ᵉ) d₃ (fun i => f₂ i olm (f₁ (d₂ i))) . *)
(* begin *)
(*   apply graded_homotopy.mk, intro i m, exact sorry *)
(* end *)

(*Definition graded_hom_out_in_rfl {d₁ d₂ : I <~> I} (f : forall i, M₁ i ->lm M₂ (d₂ i)) *)
(*   (p : forall i, d₁ i = i) : *)
(*   graded_hom.mk_out_in d₁ d₂ (fun i => sorry) ~gm graded_hom.mk d₂ f . *)
(* begin *)
(*   apply graded_homotopy.mk, intro i m, exact sorry *)
(* end *)

(*Definition graded_homotopy.trans (h₁ : f ~gm g) (h₂ : g ~gm h) : f ~gm h . *)
(* begin *)
(*   exact sorry *)
(* end *)

(* postfix `^-1ᵍᵐ`:(max + 1) . graded_iso.symm *)
--infixl ` @gm `:75 . graded_homotopy.trans
(* infixl ` @gmp `:75 . graded_iso.trans_eq *)
(* infixl ` @pgm `:75 . graded_iso.eq_trans *)


(*Definition graded_homotopy_of_deg (d : I <~> I) (f g : graded_hom_of_deg d M₁ M₂) : Type . *)
(* forall (i j : I) (p : d i = j), f p == g p *)

(* notation f ` ~[`:50 d:0 `] `:0 g:50 . graded_homotopy_of_deg d f g *)

(* variables {d : I <~> I} {f₁ f₂ : graded_hom_of_deg d M₁ M₂} *)

(*Definition graded_homotopy_of_deg.mk (h : forall i, f₁ (idpath (d i)) == f₂ (idpath (d i))) : *)
(*   f₁ ~[d] f₂ . *)
(* begin *)
(*   intro i j p, induction p, exact h i *)
(* end *)

(*Definition graded_homotopy.mk_out {M₁ M₂ : graded_module R I} (d : I <~> I) *)
(*   (fn : forall i, M₁ (d^-1 i) ->lm M₂ i) : M₁ ->gm M₂ . *)
(* graded_hom.mk' d (fun i j p => fn j olm homomorphism_of_eq (ap M₁ (eq_inv_of_eq p))) *)
(*Definition is_gconstant (f : M₁ ->gm M₂) : Type . *)
(* f↘ ~[deg f] gmd0 *)

Definition compose_constant (f' : M₂ ->gm M₃) (f : M₁ ->gm M₂) : Type.
forall (i j k : I) (p : deg f i = j) (q : deg f' j = k) (m : M₁ i), f' ↘ q (f ↘ p m) = 0

Definition compose_constant.mk (h : forall i m, f' (deg f i) (f i m) = 0) : compose_constant f' f.
by intros; induction p; induction q; exact h i m

Definition compose_constant.elim (h : compose_constant f' f) (i : I) (m : M₁ i) : f' (deg f i) (f i m) = 0.
h idp idp m

Definition is_gconstant (f : M₁ ->gm M₂) : Type.
forall (i j : I) (p : deg f i = j) (m : M₁ i), f ↘ p m = 0

Definition is_gconstant.mk (h : forall i m, f i m = 0) : is_gconstant f.
by intros; induction p; exact h i m

Definition is_gconstant.elim (h : is_gconstant f) (i : I) (m : M₁ i) : f i m = 0.
h idp m

(* direct sum of graded R-modules *)

variables {J : Set} (N : graded_module R J)
Definition dirsum' : AddAbGroup.
group.dirsum (fun j => AddAbGroup_of_LeftModule (N j))
variable {N}
Definition dirsum_smul (r : R) : dirsum' N ->a dirsum' N.
dirsum_functor (fun i => smul_homomorphism (N i) r)

Definition dirsum_smul_right_distrib (r s : R) (n : dirsum' N) :
  dirsum_smul (r + s) n = dirsum_smul r n + dirsum_smul s n.
Proof.
  refine dirsum_functor_homotopy _ _ _ n @ !dirsum_functor_mul^-1 =>
  intro i ni, exact to_smul_right_distrib r s ni
Defined.

Definition dirsum_mul_smul' (r s : R) (n : dirsum' N) :
  dirsum_smul (r * s) n = (dirsum_smul r oa dirsum_smul s) n.
Proof.
  refine dirsum_functor_homotopy _ _ _ n @ (dirsum_functor_compose _ _ n)^-1ᵖ =>
  intro i ni, exact to_mul_smul r s ni
Defined.

Definition dirsum_mul_smul (r s : R) (n : dirsum' N) :
  dirsum_smul (r * s) n = dirsum_smul r (dirsum_smul s n).
proof dirsum_mul_smul' r s n qed

Definition dirsum_one_smul (n : dirsum' N) : dirsum_smul 1 n = n.
Proof.
  refine dirsum_functor_homotopy _ _ _ n @ !dirsum_functor_gid =>
  intro i ni, exact to_one_smul ni
Defined.

Definition dirsum : LeftModule R.
LeftModule_of_AddAbGroup (dirsum' N) (fun r n => dirsum_smul r n)
  proof (fun r => homomorphism.addstruct (dirsum_smul r)) qed
  proof dirsum_smul_right_distrib qed
  proof dirsum_mul_smul qed
  proof dirsum_one_smul qed

(* graded variants of left-module constructions *)

Definition graded_submodule (S : forall i, property (M i)) [forall i, is_submodule (M i) (S i)] :
  graded_module R I.
fun i => submodule (S i)

Definition graded_submodule_incl (S : forall i, property (M i)) [H : forall i, is_submodule (M i) (S i)] :
  graded_submodule S ->gm M.
have forall i, is_submodule (M (to_fun erfl i)) (S i) => from H,
graded_hom.mk erfl deg_eq_id (fun i => submodule_incl (S i))

Definition graded_hom_lift (S : forall i, property (M₂ i)) [forall i, is_submodule (M₂ i) (S i)]
  (φ : M₁ ->gm M₂)
  (h : forall (i : I) (m : M₁ i), φ i m ∈ S (deg φ i)) : M₁ ->gm graded_submodule S.
graded_hom.mk (deg φ) (deg_eq φ) (fun i => hom_lift (φ i) (h i))

Definition graded_submodule_functor
  {S : forall i, property (M₁ i)} [forall i, is_submodule (M₁ i) (S i)]
  {T : forall i, property (M₂ i)} [forall i, is_submodule (M₂ i) (T i)]
  (φ : M₁ ->gm M₂)
  (h : forall (i : I) (m : M₁ i), S i m -> T (deg φ i) (φ i m)) :
  graded_submodule S ->gm graded_submodule T.
graded_hom.mk (deg φ) (deg_eq φ) (fun i => submodule_functor (φ i) (h i))

Definition graded_image (f : M₁ ->gm M₂) : graded_module R I.
fun i => image_module (f ← i)

lemma graded_image_lift_lemma (f : M₁ ->gm M₂) {i j: I} (p : deg f i = j) (m : M₁ i) :
  image (f ← j) (f ↘ p m).
graded_hom_change_image p (right_inv (deg f) j) (image.mk m idp)

Definition graded_image_lift (f : M₁ ->gm M₂) : M₁ ->gm graded_image f.
graded_hom.mk' (deg f) (deg_eq f) (fun i j p => hom_lift (f ↘ p) (graded_image_lift_lemma f p))

Definition graded_image_lift_destruct (f : M₁ ->gm M₂) {i : I}
  (m : M₁ ((deg f)^-1ᵉ i)) : graded_image_lift f ← i m = image_lift (f ← i) m.
subtype_eq idp

Definition graded_image.rec {f : M₁ ->gm M₂} {i : I} {P : graded_image f (deg f i) -> Type}
  [h : forall x, is_prop (P x)] (H : forall m, P (graded_image_lift f i m)) : forall m, P m.
Proof.
  assert H₂ : forall i' (p : deg f i' = deg f i) (m : M₁ i'),
  P ⟨f ↘ p m, graded_hom_change_image p _ (image.mk m idp)⟩,
  { refine eq.rec_equiv_symm (deg f) _, intro m,
  refine transport P _ (H m), apply subtype_eq, reflexivity },
  refine @total_image.rec _ _ _ _ h _, intro m,
  refine transport P _ (H₂ _ (right_inv (deg f) (deg f i)) m),
  apply subtype_eq, reflexivity
Defined.

Definition image_graded_image_lift {f : M₁ ->gm M₂} {i j : I} (p : deg f i = j)
  (m : graded_image f j)
  (h : image (f ↘ p) m.1) : image (graded_image_lift f ↘ p) m.
Proof.
  induction p,
  revert m h, refine total_image.rec _, intro m h,
  induction h with n q, refine image.mk n (subtype_eq q)
Defined.

lemma is_surjective_graded_image_lift (x y) (f : M₁ ->gm M₂)
  (p : deg f x = y) : is_surjective (graded_image_lift f ↘ p).
Proof.
  intro m, apply image_graded_image_lift, exact graded_hom_change_image (right_inv (deg f) y) _ m.2
Defined.

Definition graded_image_elim_helper {f : M₁ ->gm M₂} (g : M₁ ->gm M₃)
  (h : forall (i m), f i m = 0 -> g i m = 0) (i : I) : graded_image f (deg f i) ->lm M₃ (deg g i).
Proof.
  apply image_elim (g ↘ (ap (deg g) (to_left_inv (deg f) i))),
  intro m p,
  refine graded_hom_eq_zero I m (h _),
  exact graded_hom_eq_zero I m p
Defined.

Definition graded_image_elim {f : M₁ ->gm M₂} (g : M₁ ->gm M₃)
  (h : forall (i m), f i m = 0 -> g i m = 0) :
  graded_image f ->gm M₃.
graded_hom.mk_out_in (deg f) (deg g) (deg_eq f) (deg_eq g) (graded_image_elim_helper g h)

lemma graded_image_elim_destruct {f : M₁ ->gm M₂} {g : M₁ ->gm M₃}
  (h : forall (i m), f i m = 0 -> g i m = 0) {i j k : I}
  (p' : deg f i = j) (p : deg g ((deg f)^-1ᵉ j) = k)
  (q : deg g i = k) (r : ap (deg g) (to_left_inv (deg f) i) @ q = ap ((deg f)^-1ᵉ @e deg g) p' @ p)
  (m : M₁ i) : graded_image_elim g h ↘ p (graded_image_lift f ↘ p' m) =
  g ↘ q m.
Proof.
  revert i j p' k p q r m,
  refine equiv_rect (deg f @e (deg f)^-1ᵉ) _ _,
  intro i, refine eq.rec_grading _ (deg f) (right_inv (deg f) (deg f i)) _,
  intro k p q r m,
  assert r' : q = p,
  { refine cancel_left _ (r @ whisker_right _ _), refine !ap_compose @ ap02 (deg g) _,
  exact !adj_inv^-1 },
  induction r', clear r,
  revert k q m, refine eq.rec_to (ap (deg g) (to_left_inv (deg f) i)) _, intro m,
  refine graded_hom_mk_out_in_destruct (deg f) (deg g) (deg_eq f) (deg_eq g)
  (graded_image_elim_helper g h) (graded_image_lift f ← (deg f i) m) @ _,
  refine ap (image_elim _ _) !graded_image_lift_destruct @ _, reflexivity
Defined.

(* alternative (easier)Definition of graded_image with "wrong" grading *)

(*Definition graded_image' (f : M₁ ->gm M₂) : graded_module R I . *)
(* fun i => image_module (f i) *)

(*Definition graded_image'_lift (f : M₁ ->gm M₂) : M₁ ->gm graded_image' f . *)
(* graded_hom.mk erfl (fun i => image_lift (f i)) *)

(*Definition graded_image'_elim {f : M₁ ->gm M₂} (g : M₁ ->gm M₃) *)
(*   (h : forall (i m), f i m = 0 -> g i m = 0) : *)
(*   graded_image' f ->gm M₃ . *)
(* begin *)
(*   apply graded_hom.mk (deg g), *)
(*   intro i, *)
(*   apply image_elim (g i), *)
(*   intro m p, exact h p *)
(* end *)

(*Definition graded_image'_elim_compute {f : M₁ ->gm M₂} {g : M₁ ->gm M₃} *)
(*   (h : forall (i m), f i m = 0 -> g i m = 0) : *)
(*   graded_image'_elim g h ogm graded_image'_lift f ~gm g . *)
(* begin *)
(*   apply graded_homotopy.mk, *)
(*   intro i m, exact sorry --reflexivity *)
(* end *)

(*Definition graded_image_elim_compute {f : M₁ ->gm M₂} {g : M₁ ->gm M₃} *)
(*   (h : forall (i m), f i m = 0 -> g i m = 0) : *)
(*   graded_image_elim g h ogm graded_image_lift f ~gm g . *)
(* begin *)
(*   refine _ @gm graded_image'_elim_compute h, *)
(*   esimp, exact sorry *)
(*   (* refine graded_hom_out_in_compose_out _ _ @gm _, exact sorry *) *)
(*   (* (* apply graded_homotopy.mk, *) *) *)
(*   (* (* intro i m, *) *) *)
(* end *)

(* variables {α β : I <~> I} *)
(*Definition gen_image (f : M₁ ->gm M₂) (p : forall i, deg f (α i) = β i) : graded_module R I . *)
(* fun i => image_module (f ↘ (p i)) *)

(*Definition gen_image_lift (f : M₁ ->gm M₂) (p : forall i, deg f (α i) = β i) : M₁ ->gm gen_image f p . *)
(* graded_hom.mk_out α^-1ᵉ (fun i => image_lift (f ↘ (p i))) *)

(*Definition gen_image_elim {f : M₁ ->gm M₂} (p : forall i, deg f (α i) = β i) (g : M₁ ->gm M₃) *)
(*   (h : forall (i m), f i m = 0 -> g i m = 0) : *)
(*   gen_image f p ->gm M₃ . *)
(* begin *)
(*   apply graded_hom.mk_out_in α^-1ᵉ (deg g), *)
(*   intro i, *)
(*   apply image_elim (g ↘ (ap (deg g) (to_right_inv α i))), *)
(*   intro m p, *)
(*   refine graded_hom_eq_zero m (h _), *)
(*   exact graded_hom_eq_zero m p *)
(* end *)

(*Definition gen_image_elim_compute {f : M₁ ->gm M₂} {p : deg f o α == β} {g : M₁ ->gm M₃} *)
(*   (h : forall (i m), f i m = 0 -> g i m = 0) : *)
(*   gen_image_elim p g h ogm gen_image_lift f p ~gm g . *)
(* begin *)
(*   (* induction β with β βe, esimp at *, induction p using homotopy.rec_on_idp, *) *)
(*   assert q : β @e (deg f)^-1ᵉ = α, *)
(*   { apply equiv_eq, intro i, apply inv_eq_of_eq, exact (p i)^-1 }, *)
(*   induction q, *)
(*   (* unfold [gen_image_elim, gen_image_lift], *) *)

(*   (* induction (is_prop.elim (fun i => to_right_inv (deg f) (β i)) p), *) *)
(*   (* apply graded_homotopy.mk, *) *)
(*   (* intro i m, reflexivity *) *)
(*   exact sorry *)
(* end *)

Definition graded_kernel (f : M₁ ->gm M₂) : graded_module R I.
fun i => kernel_module (f i)

Definition graded_quotient (S : forall i, property (M i)) [forall i, is_submodule (M i) (S i)] : graded_module R I.
fun i => quotient_module (S i)

Definition graded_quotient_map (S : forall i, property (M i)) [forall i, is_submodule (M i) (S i)] :
  M ->gm graded_quotient S.
graded_hom.mk erfl deg_eq_id (fun i => quotient_map (S i))

Definition graded_quotient_elim
  (S : forall i, property (M i)) [forall i, is_submodule (M i) (S i)]
  (φ : M ->gm M₂)
  (H : forall i (m), S i m -> φ i m = 0) : graded_quotient S ->gm M₂.
graded_hom.mk (deg φ) (deg_eq φ) (fun i => quotient_elim (φ i) (H i))

Definition graded_homology (g : M₂ ->gm M₃) (f : M₁ ->gm M₂) : graded_module R I.
graded_quotient (fun i => homology_quotient_property (g i) (f ← i))

(* the two reasonableDefinitions of graded_homology areDefinitionally equal *)
example (g : M₂ ->gm M₃) (f : M₁ ->gm M₂) :
  (fun i => homology (g i) (f ← i)) = graded_homology g f . idp

Definition graded_homology.mk (g : M₂ ->gm M₃) (f : M₁ ->gm M₂) {i : I} (m : M₂ i) (h : g i m = 0) :
  graded_homology g f i.
homology.mk _ m h

Definition graded_homology_intro (g : M₂ ->gm M₃) (f : M₁ ->gm M₂) :
  graded_kernel g ->gm graded_homology g f.
@graded_quotient_map _ _ _ (fun i => homology_quotient_property (g i) (f ← i)) _

Definition graded_homology_elim {g : M₂ ->gm M₃} {f : M₁ ->gm M₂} (h : M₂ ->gm M)
  (H : compose_constant h f) : graded_homology g f ->gm M.
graded_hom.mk (deg h) (deg_eq h) (fun i => homology_elim (h i) (H _ _))

Definition graded_homology_isomorphism (g : M₂ ->gm M₃) (f : M₁ ->gm M₂) (x : I) :
  graded_homology g f (deg f x) <~>lm homology (g (deg f x)) (f x).
Proof.
  refine homology_isomorphism_homology (isomorphism_of_eq (ap M₁ (left_inv (deg f) x)))
  isomorphism.rfl isomorphism.rfl homotopy.rfl _,
  exact graded_hom_square f (to_right_inv (deg f) (deg f x)) idp (to_left_inv (deg f) x) idp
Defined.

Definition graded_homology_isomorphism_kernel_module
  (g : M₂ ->gm M₃) (f : M₁ ->gm M₂) (x : I)
  (H : forall m, image (f ← x) m -> m = 0) : graded_homology g f x <~>lm graded_kernel g x.
Proof.
  apply quotient_module_isomorphism, intro m h, apply subtype_eq, apply H, exact h
Defined.

Definition image_of_graded_homology_intro_eq_zero {g : M₂ ->gm M₃} {f : M₁ ->gm M₂}
  (i j : I) (p : deg f i = j) (m : graded_kernel g j) (H : graded_homology_intro g f j m = 0) :
  image (f ↘ p) m.1.
Proof.
  induction p, exact graded_hom_change_image _ _
  (@rel_of_quotient_map_eq_zero _ _ _ _ m H)
Defined.

Definition is_exact_gmod (f : M₁ ->gm M₂) (f' : M₂ ->gm M₃) : Type.
forall (i j k) (p : deg f i = j) (q : deg f' j = k), is_exact_mod (f ↘ p) (f' ↘ q)

Definition is_exact_gmod.mk {f : M₁ ->gm M₂} {f' : M₂ ->gm M₃}
  (h₁ : forall (i) (m : M₁ i), f' (deg f i) (f i m) = 0)
  (h₂ : forall (i) (m : M₂ (deg f i)), f' (deg f i) m = 0 -> image (f i) m) : is_exact_gmod f f'.
Proof. intro i j k p q; induction p; induction q; split, apply h₁, apply h₂ end

Definition gmod_im_in_ker (h : is_exact_gmod f f') : compose_constant f' f.
fun i j k p q => is_exact.im_in_ker (h p q)

Definition gmod_ker_in_im (h : is_exact_gmod f f') (i : I) (m : M₂ i) (p : f' i m = 0) :
  image (f ← i) m.
is_exact.ker_in_im (h (right_inv (deg f) i) idp) m p

Definition is_exact_gmod_reindex {J : AddGroup} (e : J <~>g I) (h : is_exact_gmod f f') :
  is_exact_gmod (graded_hom_reindex e f) (graded_hom_reindex e f').
fun i j k p q => h (eq_of_inv_eq p) (eq_of_inv_eq q)

Definition deg_commute {I : AddAbGroup} {M₁ M₂ M₃ M₄ : graded_module R I} (f : M₁ ->gm M₂)
  (g : M₃ ->gm M₄) : hsquare (deg f) (deg f) (deg g) (deg g).
Proof.
  intro i,
  refine ap (deg g) (deg_eq f i) @ deg_eq g _ @ _ @ (ap (deg f) (deg_eq g i) @ deg_eq f _)^-1,
  exact !add.assoc @ ap (fun x => i + x) !add.comm @ !add.assoc^-1
Defined.


Defined. left_module
