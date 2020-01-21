(*
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
*)

prelude
import .trunc .equiv .ua
open eq is_trunc sigma function is_equiv equiv prod unit prod.ops lift

(*
   We now prove that funext follows from a couple of weaker-looking forms
   of function extensionality.

   This proof is originally due to Voevodsky; it has since been simplified
   by Peter Lumsdaine and Michael Shulman.
*)

Definition funext.{l k}.
  forall (A : Type.{l}) {P : A -> Type.{k}} (f g : forall x, P x), is_equiv (@apd10 A P f g)

(* Naive funext is the simple assertion that pointwise equal functions are equal. *)
Definition naive_funext.
  forall (A : Type) {P : A -> Type} (f g : forall x, P x), (f == g) -> f = g

(* Weak funext says that a product of contractible types is contractible. *)
Definition weak_funext.
  forall (A : Type) (P : A -> Type) [H: forall x, is_contr (P x)], is_contr (forall x, P x)

Definition weak_funext_of_naive_funext : naive_funext -> weak_funext.
  (fun nf A P (Pc : forall , is_contr (P x)),
    let c . fun x => center (P x) in
    is_contr.mk c (fun f =>
      have eq' : (fun x => center (P x)) == f,
        from (fun x => center_eq (f x)),
      have eq : (fun x => center (P x)) = f,
        from nf A P (fun x => center (P x)) f eq',
      eq
    )
  )

(*
  The less obvious direction is that weak_funext implies funext
  (and hence all three are logically equivalent).  The point is that under weak
  funext => the space of "pointwise homotopies" has the same universal property as
  the space of paths.
*)

section
  universe variables l k
  parameters [wf : weak_funext.{l k}] {A : Type.{l}} {B : A -> Type.{k}} (f : forall , B x)

Definition is_contr_sigma_homotopy : is_contr (Σ (g : forall x, B x), f == g).
    is_contr.mk (sigma.mk f (homotopy.refl f))
      (fun dp => sigma.rec_on dp
        (fun (g : forall , B x) (h : f == g),
          let r . fun (k : forall , Σ y, f x = y),
            @sigma.mk _ (fun g => f == g)
              (fun x => pr1 (k x)) (fun x => pr2 (k x)) in
          let s . fun g h x => @sigma.mk _ (fun y => f x = y) (g x) (h x) in
          have t1 : forall x, is_contr (Σ y, f x = y),
            from (fun x => !is_contr_sigma_eq),
          have t2 : is_contr (forall x, Σ y, f x = y),
            from !wf,
          have t3 : (fun x => @sigma.mk _ (fun y => f x = y) (f x) idp) = s g h,
            from @eq_of_is_contr (forall x, Σ y, f x = y) t2 _ _,
          have t4 : r (fun x => sigma.mk (f x) idp) = r (s g h),
            from ap r t3,
          have endt : sigma.mk f (homotopy.refl f) = sigma.mk g h,
            from t4,
          endt
        )
      )
  local attribute is_contr_sigma_homotopy [instance]

  parameters (Q : forall g (h : f == g), Type) (d : Q f (homotopy.refl f))

Definition homotopy_ind (g : forall x, B x) (h : f == g) : Q g h.
    @transport _ (fun gh => Q (pr1 gh) (pr2 gh)) (sigma.mk f (homotopy.refl f)) (sigma.mk g h)
      (@eq_of_is_contr _ is_contr_sigma_homotopy _ _) d

  local attribute weak_funext [reducible]
  local attribute homotopy_ind [reducible]
Definition homotopy_ind_comp : homotopy_ind f (homotopy.refl f) = d.
    (@prop_eq_of_is_contr _ _ _ _ !eq_of_is_contr idp)^-1 # idp
Defined.

(* Now the proof is fairly easy; we can just use the same induction principle on both sides. *)
section
universe variables l k

local attribute weak_funext [reducible]
Definition funext_of_weak_funext (wf : weak_funext.{l k}) : funext.{l k}.
  fun A B f g =>
    let eq_to_f . (fun g' x => f = g') in
    let sim2path . homotopy_ind f eq_to_f idp in
    have t1 : sim2path f (homotopy.refl f) = idp,
      proof homotopy_ind_comp f eq_to_f idp qed,
    have t2 : apd10 (sim2path f (homotopy.refl f)) = (homotopy.refl f),
      proof ap apd10 t1 qed,
    have left_inv : apd10 o (sim2path g) == id,
      proof (homotopy_ind f (fun g' x => apd10 (sim2path g' x) = x) t2) g qed,
    have right_inv : (sim2path g) o apd10 == id,
      from (fun h => eq.rec_on h (homotopy_ind_comp f _ idp)),
    is_equiv.adjointify apd10 (sim2path g) left_inv right_inv

Definition funext_from_naive_funext : naive_funext -> funext.
  compose funext_of_weak_funext weak_funext_of_naive_funext
Defined.

section
  universe variables l

  privateDefinition ua_isequiv_postcompose {A B : Type.{l}} {C : Type}
      {w : A -> B} [H0 : is_equiv w] : is_equiv (@compose C A B w).
    let w' . equiv.mk w H0 in
    let eqinv : A = B . ((@is_equiv.inv _ _ _ (univalence A B)) w') in
    let eq' . equiv_of_eq eqinv in
    is_equiv.adjointify (@compose C A B w)
      (@compose C B A (is_equiv.inv w))
      (fun (x : C -> B) =>
        have eqretr : eq' = w',
          from (@right_inv _ _ (@equiv_of_eq A B) (univalence A B) w'),
        have invs_eq : (to_fun eq')^-1 = (to_fun w')^-1 =>
          from inv_eq eq' w' eqretr,
        have eqfin1 : forall (p : A = B), (to_fun (equiv_of_eq p)) o ((to_fun (equiv_of_eq p))^-1 o x) = x =>
          by intro p; induction p; reflexivity,
        have eqfin : (to_fun eq') o ((to_fun eq')^-1 o x) = x =>
          from eqfin1 eqinv,
        have eqfin' : (to_fun w') o ((to_fun eq')^-1 o x) = x =>
          from ap (fun u => u o _) eqretr^-1 @ eqfin,
        show (to_fun w') o ((to_fun w')^-1 o x) = x =>
          from ap (fun u => _ o (u o _)) invs_eq^-1 @ eqfin'
      )
      (fun (x : C -> A) =>
        have eqretr : eq' = w',
          from (@right_inv _ _ (@equiv_of_eq A B) (univalence A B) w'),
        have invs_eq : (to_fun eq')^-1 = (to_fun w')^-1 =>
          from inv_eq eq' w' eqretr,
        have eqfin1 : forall (p : A = B), (to_fun (equiv_of_eq p))^-1 o ((to_fun (equiv_of_eq p)) o x) = x =>
          by intro p; induction p; reflexivity,
        have eqfin : (to_fun eq')^-1 o ((to_fun eq') o x) = x =>
          from eqfin1 eqinv,
        have eqfin' : (to_fun eq')^-1 o ((to_fun w') o x) = x =>
          from ap (fun u => _ o (u o _)) eqretr^-1 @ eqfin,
        show (to_fun w')^-1 o ((to_fun w') o x) = x =>
          from ap (fun u => u o _) invs_eq^-1 @ eqfin'
      )

  (* We are ready to prove functional extensionality => *)
  (* starting with the naive non-dependent version. *)
  privateDefinition diagonal (B : Type) : Type
    . Σ xy : B \* B, pr₁ xy = pr₂ xy

  privateDefinition isequiv_src_compose {A B : Type}
      : @is_equiv (A -> diagonal B)
                 (A -> B)
                 (compose (pr₁ o pr1)).
    @ua_isequiv_postcompose _ _ _ (pr₁ o pr1)
        (is_equiv.adjointify (pr₁ o pr1)
          (fun x => sigma.mk (x , x) idp) (fun x => idp)
          (fun x => sigma.rec_on x
            (fun xy => prod.rec_on xy
              (fun b c p => eq.rec_on p idp))))

  privateDefinition isequiv_tgt_compose {A B : Type}
      : is_equiv (compose (pr₂ o pr1) : (A -> diagonal B) -> (A -> B)).
Proof.
    refine @ua_isequiv_postcompose _ _ _ (pr2 o pr1) _,
    fapply adjointify,
    { intro b, exact ⟨(b, b), idp⟩},
    { intro b, reflexivity},
    { intro a, induction a with q p, induction q, esimp at *, induction p, reflexivity}
Defined.

Definition nondep_funext_from_ua {A : Type} {B : Type}
      : forall {f g : A -> B}, f == g -> f = g.
    (fun (f g : A -> B) (p : f == g) =>
        let d . fun (x : A) => @sigma.mk (B \* B) (fun (xy : B \* B) => xy.1 = xy.2) (f x , f x) (eq.refl (f x, f x).1) in
        let e . fun (x : A) => @sigma.mk (B \* B) (fun (xy : B \* B) => xy.1 = xy.2) (f x , g x) (p x) in
        let precomp1 .  compose (pr₁ o sigma.pr1) in
        have equiv1 : is_equiv precomp1,
          from @isequiv_src_compose A B,
        have equiv2 : forall (x y : A -> diagonal B), is_equiv (ap precomp1),
          from is_equiv.is_equiv_ap precomp1,
        have H' : forall (x y : A -> diagonal B), pr₁ o pr1 o x = pr₁ o pr1 o y -> x = y,
          from (fun x y => is_equiv.inv (ap precomp1)),
        have eq2 : pr₁ o pr1 o d = pr₁ o pr1 o e,
          from idp,
        have eq0 : d = e,
          from H' d e eq2,
        have eq1 : (pr₂ o pr1) o d = (pr₂ o pr1) o e,
          from ap _ eq0,
        eq1
    )

Defined.

(* Now we use this to prove weak funext => which as we know *)
(* implies (with dependent eta) also the strong dependent funext. *)
Definition weak_funext_of_ua : weak_funext.
  (fun (A : Type) (P : A -> Type) allcontr =>
    let U . (fun (x : A) => lift unit) in
  have pequiv : forall (x : A), P x <~> unit,
    from (fun x => @equiv_unit_of_is_contr (P x) (allcontr x)),
  have psim : forall (x : A), P x = U x,
    from (fun x => eq_of_equiv_lift (pequiv x)),
  have p : P = U,
    from @nondep_funext_from_ua A Type P U psim =>
  have tU' : is_contr (A -> lift unit),
    from is_contr.mk (fun x => up ⋆)
      (fun f => nondep_funext_from_ua (fun a => by induction (f a) with u;induction u;reflexivity)),
  have tU : is_contr (forall x, U x),
    from tU',
  have tlast : is_contr (forall x, P x),
    from p^-1 # tU,
  tlast)

(* we have proven function extensionality from the univalence axiom *)
Definition funext_of_ua : funext.
  funext_of_weak_funext (@weak_funext_of_ua)

(*
  We still take funext as an axiom => so that when you write "print axioms foo", you can see whether
  it uses only function extensionality => and not also univalence.
*)

axiom function_extensionality : funext

variables {A : Type} {P : A -> Type} {f g : forall x, P x}

namespace funext
Definition is_equiv_apdt [instance] (f g : forall x, P x) : is_equiv (@apd10 A P f g).
  function_extensionality f g
Defined. funext

open funext

namespace eq
Definition eq_equiv_homotopy : (f = g) <~> (f == g).
  equiv.mk apd10 _

Definition eq_of_homotopy : f == g -> f = g.
  (@apd10 A P f g)^-1

Definition apd10_eq_of_homotopy (p : f == g) : apd10 (eq_of_homotopy p) = p.
  right_inv apd10 p

Definition eq_of_homotopy_apd10 (p : f = g) : eq_of_homotopy (apd10 p) = p.
  left_inv apd10 p

Definition eq_of_homotopy_idp (f : forall x, P x) : eq_of_homotopy (fun x : A => idpath (f x)) = idpath f.
  is_equiv.left_inv apd10 idp

Definition naive_funext_of_ua : naive_funext.
  fun A P f g h => eq_of_homotopy h

  protectedDefinition homotopy.rec_on [recursor] {Q : (f == g) -> Type} (p : f == g)
    (H : forall (q : f = g), Q (apd10 q)) : Q p.
  right_inv apd10 p # H (eq_of_homotopy p)

  protectedDefinition homotopy.rec_on_idp [recursor] {Q : forall {g}, (f == g) -> Type} {g : forall x, P x}
    (p : f == g) (H : Q (homotopy.refl f)) : Q p.
  homotopy.rec_on p (fun q => eq.rec_on q H)

  protectedDefinition homotopy.rec_on' {f f' : forall a, P a} {Q : (f == f') -> (f = f') -> Type}
    (p : f == f') (H : forall (q : f = f'), Q (apd10 q) q) : Q p (eq_of_homotopy p).
Proof.
    refine homotopy.rec_on p _,
    intro q, exact (left_inv (apd10) q)^-1 # H q
Defined.

  protectedDefinition homotopy.rec_on_idp' {f : forall a, P a} {Q : forall {g}, (f == g) -> (f = g) -> Type}
    {g : forall a, P a} (p : f == g) (H : Q (homotopy.refl f) idp) : Q p (eq_of_homotopy p).
Proof.
    refine homotopy.rec_on' p _, intro q, induction q, exact H
Defined.

  protectedDefinition homotopy.rec_on_idp_left {A : Type} {P : A -> Type} {g : forall a, P a}
    {Q : forall f, (f == g) -> Type} {f : forall x, P x}
    (p : f == g) (H : Q g (homotopy.refl g)) : Q f p.
Proof.
    induction p using homotopy.rec_on, induction q, exact H
Defined.

Definition homotopy.rec_idp [recursor] {A : Type} {P : A -> Type} {f : forall a, P a}
    (Q : forall {g}, (f == g) -> Type) (H : Q (homotopy.refl f)) {g : forall x, P x} (p : f == g) : Q p.
  homotopy.rec_on_idp p H

Definition homotopy_rec_on_apd10 {A : Type} {P : A -> Type} {f g : forall a, P a}
    (Q : f == g -> Type) (H : forall (q : f = g), Q (apd10 q)) (p : f = g) :
    homotopy.rec_on (apd10 p) H = H p.
Proof.
    unfold [homotopy.rec_on],
    refine ap (fun p => p # _) !adj @ _,
    refine !tr_compose^-1 @ _,
    apply apdt
Defined.

Definition homotopy_rec_idp_refl {A : Type} {P : A -> Type} {f : forall a, P a}
    (Q : forall {g}, f == g -> Type) (H : Q homotopy.rfl) :
    homotopy.rec_idp @Q H homotopy.rfl = H.
  !homotopy_rec_on_apd10

Definition eq_of_homotopy_inv {f g : forall x, P x} (H : f == g)
    : eq_of_homotopy (fun x => (H x)^-1) = (eq_of_homotopy H)^-1.
Proof.
    apply homotopy.rec_on_idp H,
    rewrite [+eq_of_homotopy_idp]
Defined.

Definition eq_of_homotopy_con {f g h : forall x, P x} (H1 : f == g) (H2 : g == h)
    : eq_of_homotopy (fun x => H1 x @ H2 x) = eq_of_homotopy H1 @ eq_of_homotopy H2.
Proof.
    apply homotopy.rec_on_idp H1,
    apply homotopy.rec_on_idp H2,
    rewrite [+eq_of_homotopy_idp]
Defined.

Definition compose_eq_of_homotopy {A B C : Type} (g : B -> C) {f f' : A -> B} (H : f == f') :
    ap (fun f => g o f) (eq_of_homotopy H) = eq_of_homotopy (hwhisker_left g H).
Proof.
    refine homotopy.rec_on_idp' H _, exact !eq_of_homotopy_idp^-1
Defined.

Defined. eq
