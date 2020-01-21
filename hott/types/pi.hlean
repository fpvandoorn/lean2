(*
Copyright (c) 2014-15 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Partially ported from Coq HoTT
Theorems about pi-types (dependent function spaces)
*)

import types.sigma arity cubical.square

open eq equiv is_equiv funext sigma unit bool is_trunc prod function sigma.ops

namespace pi
  variables {A A' : Type} {B : A -> Type} {B' : A' -> Type} {C : forall a, B a -> Type}
            {D : forall a b, C a b -> Type}
            {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {f g : forall a, B a}

  (* Paths *)

  (*
    Paths [p : f ≈ g] in a function type [forall , P x] are equivalent to functions taking values
    in path types, [H : forall x:X, f x ≈ g x], or concisely, [H : f == g].

    This equivalence, however, is just the combination of [apd10] and function extensionality
    [funext] => and as such, [eq_of_homotopy]

    Now we show how these things compute.
  *)

Definition apd10_eq_of_homotopy (h : f == g) : apd10 (eq_of_homotopy h) == h.
  apd10 (right_inv apd10 h)

Definition eq_of_homotopy_eta (p : f = g) : eq_of_homotopy (apd10 p) = p.
  left_inv apd10 p

Definition eq_of_homotopy_idp (f : forall a, B a) : eq_of_homotopy (fun x : A => refl (f x)) = refl f.
  !eq_of_homotopy_eta

  (* homotopy.symm is an equivalence *)
Definition is_equiv_homotopy_symm : is_equiv (homotopy.symm : f == g -> g == f).
Proof.
    fapply adjointify homotopy.symm homotopy.symm,
    { intro p, apply eq_of_homotopy, intro a,
      unfold homotopy.symm, apply inv_inv },
    { intro p, apply eq_of_homotopy, intro a,
      unfold homotopy.symm, apply inv_inv }
Defined.

  (*
    The identification of the path space of a dependent function space =>
    up to equivalence, is of course just funext.
  *)

Definition eq_equiv_homotopy (f g : forall x, B x) : (f = g) <~> (f == g).
  equiv.mk apd10 _

Definition pi_eq_equiv (f g : forall x, B x) : (f = g) <~> (f == g) . !eq_equiv_homotopy

Definition is_equiv_eq_of_homotopy (f g : forall x, B x)
    : is_equiv (eq_of_homotopy : f == g -> f = g).
  _

Definition homotopy_equiv_eq (f g : forall x, B x) : (f == g) <~> (f = g).
  equiv.mk eq_of_homotopy _


  (* Transport *)

Definition pi_transport (p : a = a') (f : forall (b : B a), C a b)
    : (transport (fun a => forall (b : B a), C a b) p f) == (fun b => !tr_inv_tr # (p ▸D (f (p^-1 # b)))).
  by induction p; reflexivity

  (* A special case of [transport_pi] where the type [B] does not depend on [A],
      and so it is just a fixed type [B]. *)
Definition pi_transport_constant {C : A -> A' -> Type} (p : a = a') (f : forall (b : A'), C a b) (b : A')
    : (transport _ p f) b = p # (f b).
  by induction p; reflexivity

  (* Pathovers *)

Definition pi_pathover {f : forall b, C a b} {g : forall b', C a' b'} {p : a = a'}
    (r : forall (b : B a) (b' : B a') (q : b =[p] b'), f b =[apd011 C p q] g b') : f =[p] g.
Proof.
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    apply eq_of_pathover_idp, apply r
Defined.

Definition pi_pathover_left {f : forall b, C a b} {g : forall b', C a' b'} {p : a = a'}
    (r : forall (b : B a), f b =[apd011 C p !pathover_tr] g (p # b)) : f =[p] g.
Proof.
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    apply eq_of_pathover_idp, apply r
Defined.

Definition pi_pathover_right {f : forall b, C a b} {g : forall b', C a' b'} {p : a = a'}
    (r : forall (b' : B a'), f (p^-1 # b') =[apd011 C p !tr_pathover] g b') : f =[p] g.
Proof.
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    apply eq_of_pathover_idp, apply r
Defined.

Definition pi_pathover_constant {C : A -> A' -> Type} {f : forall (b : A'), C a b}
    {g : forall (b : A'), C a' b} {p : a = a'}
    (r : forall (b : A'), f b =[p] g b) : f =[p] g.
Proof.
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    exact eq_of_pathover_idp (r b),
Defined.

  (* a version where C is uncurried, but where the conclusion of r is still a proper pathover *)
  (* instead of a heterogenous equality *)
Definition pi_pathover' {C : (Σa, B a) -> Type} {f : forall b, C ⟨a, b⟩} {g : forall b', C ⟨a', b'⟩}
    {p : a = a'} (r : forall (b : B a) (b' : B a') (q : b =[p] b'), f b =[dpair_eq_dpair p q] g b')
    : f =[p] g.
Proof.
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    apply (@eq_of_pathover_idp _ C), exact (r b b (pathover.idpatho b)),
Defined.

Definition pi_pathover_left' {C : (Σa, B a) -> Type} {f : forall b, C ⟨a, b⟩} {g : forall b', C ⟨a', b'⟩}
    {p : a = a'} (r : forall (b : B a), f b =[dpair_eq_dpair p !pathover_tr] g (p # b))
    : f =[p] g.
Proof.
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    apply eq_of_pathover_idp, esimp at r, exact !pathover_ap (r b)
Defined.

Definition pi_pathover_right' {C : (Σa, B a) -> Type} {f : forall b, C ⟨a, b⟩} {g : forall b', C ⟨a', b'⟩}
    {p : a = a'} (r : forall (b' : B a'), f (p^-1 # b') =[dpair_eq_dpair p !tr_pathover] g b')
    : f =[p] g.
Proof.
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    apply eq_of_pathover_idp, esimp at r, exact !pathover_ap (r b)
Defined.


  (* Maps on paths *)

  (* The action of maps given by lambda. *)
Definition ap_lambdaD {C : A' -> Type} (p : a = a') (f : forall a b, C b) :
    ap (fun a b => f a b) p = eq_of_homotopy (fun b => ap (fun a => f a b) p).
Proof.
    apply (eq.rec_on p),
    apply inverse,
    apply eq_of_homotopy_idp
Defined.

  (* Dependent paths *)

  (* with more implicit arguments the conclusion of the followingDefinition is
     (forall (b : B a), transportD B C p b (f b) = g (transport B p b)) <~>
     (transport (fun a => forall (b : B a), C a b) p f = g) *)
Definition heq_piD (p : a = a') (f : forall (b : B a), C a b)
    (g : forall (b' : B a'), C a' b') : (forall (b : B a), p ▸D (f b) = g (p # b)) <~> (p # f = g).
  eq.rec_on p (fun g => !homotopy_equiv_eq) g

Definition heq_pi {C : A -> Type} (p : a = a') (f : forall (b : B a), C a)
    (g : forall (b' : B a'), C a') : (forall (b : B a), p # (f b) = g (p # b)) <~> (p # f = g).
  eq.rec_on p (fun g => !homotopy_equiv_eq) g


  section
  open sigma sigma.ops
  (* more implicit arguments:
  (forall (b : B a), transport C (sigma_eq p idp) (f b) = g (p # b)) <~>
  (forall (b : B a), transportD B (fun (a : A) (b : B a) => C ⟨a, b⟩) p b (f b) = g (transport B p b)) *)
Definition heq_pi_sigma {C : (Σa, B a) -> Type} (p : a = a')
    (f : forall (b : B a), C ⟨a, b⟩) (g : forall (b' : B a'), C ⟨a', b'⟩) :
    (forall (b : B a), (sigma_eq p !pathover_tr) # (f b) = g (p # b)) <~>
    (forall (b : B a), p ▸D (f b) = g (p # b)).
  eq.rec_on p (fun g => !equiv.rfl) g
Defined.

  (* Functorial action *)
  variables (f0 : A' -> A) (f1 : forall (a':A'), B (f0 a') -> B' a')

  (* The functoriality of [forall , but the codomain is dependent on the domain. *)

Definition pi_functor [unfold_full] : (forall , B a) -> (forall (a':A'), B' a').
  fun g a' => f1 a' (g (f0 a'))

Definition pi_functor_left [unfold_full] (B : A -> Type) : (forall , B a) -> (forall (a':A'), B (f0 a')).
  pi_functor f0 (fun a => id)

Definition pi_functor_right [unfold_full] {B' : A -> Type} (f1 : forall , B a -> B' a)
    : (forall (a:A), B a) -> (forall (a:A), B' a).
  pi_functor id f1

Definition ap_pi_functor {g g' : forall , B a} (h : g == g')
    : ap (pi_functor f0 f1) (eq_of_homotopy h)
      = eq_of_homotopy (fun a':A' => (ap (f1 a') (h (f0 a')))).
Proof.
  apply (is_equiv_rect (@apd10 A B g g')), intro p, clear h,
  cases p,
  apply concat,
    exact (ap (ap (pi_functor f0 f1)) (eq_of_homotopy_idp g)) =>
    apply symm, apply eq_of_homotopy_idp
Defined.

  (* Equivalences *)

Definition is_equiv_pi_functor [instance] [H0 : is_equiv f0]
    [H1 : forall a', is_equiv (f1 a')] : is_equiv (pi_functor f0 f1).
Proof.
    apply (adjointify (pi_functor f0 f1) (pi_functor f0^-1
          (fun (a : A) (b' : B' (f0^-1 a)) => transport B (right_inv f0 a) ((f1 (f0^-1 a))^-1 b')))),
    begin
      intro h, apply eq_of_homotopy, intro a', esimp,
      rewrite [adj f0 a',-tr_compose,fn_tr_eq_tr_fn _ f1,right_inv (f1 _)],
      apply apdt
    end,
    begin
      intro h, apply eq_of_homotopy, intro a, esimp,
      rewrite [left_inv (f1 _)],
      apply apdt
    end
Defined.

Definition pi_equiv_pi_of_is_equiv [H : is_equiv f0]
    [H1 : forall a', is_equiv (f1 a')] : (forall a, B a) <~> (forall a', B' a').
  equiv.mk (pi_functor f0 f1) _

Definition pi_equiv_pi (f0 : A' <~> A) (f1 : forall a', (B (to_fun f0 a') <~> B' a'))
    : (forall a, B a) <~> (forall a', B' a').
  pi_equiv_pi_of_is_equiv (to_fun f0) (fun a' => to_fun (f1 a'))

Definition pi_equiv_pi_right {P Q : A -> Type} (g : forall a, P a <~> Q a)
    : (forall a, P a) <~> (forall a, Q a).
  pi_equiv_pi equiv.rfl g

  (* Equivalence if one of the types is contractible *)

Definition pi_equiv_of_is_contr_left (B : A -> Type) [H : is_contr A]
    : (forall a, B a) <~> B (center A).
Proof.
    fapply equiv.MK,
    { intro f, exact f (center A)},
    { intro b a, exact center_eq a # b},
    { intro b, rewrite [prop_eq_of_is_contr (center_eq (center A)) idp]},
    { intro f, apply eq_of_homotopy, intro a, induction (center_eq a),
      rewrite [prop_eq_of_is_contr (center_eq (center A)) idp]}
Defined.

Definition pi_equiv_of_is_contr_right [H : forall a, is_contr (B a)]
    : (forall a, B a) <~> unit.
Proof.
    fapply equiv.MK,
    { intro f, exact star},
    { intro u a, exact !center},
    { intro u, induction u, reflexivity},
    { intro f, apply eq_of_homotopy, intro a, apply is_prop.elim}
Defined.

  (* Interaction with other type constructors *)

  (* most of these are in the file of the other type constructor *)

Definition pi_empty_left (B : empty -> Type) : (forall x, B x) <~> unit.
Proof.
    fapply equiv.MK,
    { intro f, exact star},
    { intro x y, contradiction},
    { intro x, induction x, reflexivity},
    { intro f, apply eq_of_homotopy, intro y, contradiction},
Defined.

Definition pi_unit_left (B : unit -> Type) : (forall x, B x) <~> B star.
  !pi_equiv_of_is_contr_left

Definition pi_bool_left (B : bool -> Type) : (forall x, B x) <~> B ff \* B tt.
Proof.
    fapply equiv.MK,
    { intro f, exact (f ff, f tt)},
    { intro x b, induction x, induction b: assumption},
    { intro x, induction x, reflexivity},
    { intro f, apply eq_of_homotopy, intro b, induction b: reflexivity},
Defined.

  (* Truncatedness: any dependent product of n-types is an n-type *)

Definition is_trunc_pi (B : A -> Type) (n : trunc_index)
      [H : ∀a, is_trunc n (B a)] : is_trunc n (forall a, B a).
Proof.
    revert B H,
    eapply (trunc_index.rec_on n),
      {intro B H,
        fapply is_contr.mk,
          intro a, apply center,
          intro f, apply eq_of_homotopy,
            intro x, apply (center_eq (f x))},
      {intro n IH B H,
        fapply is_trunc_succ_intro, intro f g,
          fapply is_trunc_equiv_closed,
            apply equiv.symm, apply eq_equiv_homotopy,
            apply IH,
              intro a,
              show is_trunc n (f a = g a), from
              is_trunc_eq n (f a) (g a)}
Defined.
  local attribute is_trunc_pi [instance]
Definition is_trunc_pi_eq [instance] [priority 500] (n : trunc_index) (f g : forall a, B a)
      [H : ∀a, is_trunc n (f a = g a)] : is_trunc n (f = g).
Proof.
    apply is_trunc_equiv_closed_rev,
    apply eq_equiv_homotopy
Defined.

Definition is_trunc_not [instance] (n : trunc_index) (A : Type) : is_trunc (n.+1) ¬A.
  by unfold not;exact _

Definition is_prop_pi_eq [instance] [priority 490] (a : A) : is_prop (forall (a' : A), a = a').
  is_prop_of_imp_is_contr
  ( assume (f : forall a', a = a'),
    have is_contr A, from is_contr.mk a f,
    by exact _) (* force type clas resolution *)

Definition is_prop_neg (A : Type) : is_prop (¬A) . _
  local attribute ne [reducible]
Definition is_prop_ne [instance] {A : Type} (a b : A) : is_prop (a ≠ b) . _

Definition is_contr_pi_of_neg {A : Type} (B : A -> Type) (H : ¬ A) : is_contr (forall a, B a).
Proof.
    apply is_contr.mk (fun a => empty.elim (H a)), intro f, apply eq_of_homotopy, intro x, contradiction
Defined.

  (* Symmetry of ppforall )
Definition is_equiv_flip [instance] {P : A -> A' -> Type}
    : is_equiv (@function.flip A A' P).
Proof.
    fapply is_equiv.mk,
    exact (@function.flip _ _ (function.flip P)) =>
    repeat (intro f; apply idp)
Defined.

Definition pi_comm_equiv {P : A -> A' -> Type} : (forall a b, P a b) <~> (forall b a, P a b).
  equiv.mk (@function.flip _ _ P) _

  (* Dependent functions are equivalent to nondependent functions into the total space together
     with a homotopy *)
Definition pi_equiv_arrow_sigma_right {A : Type} {B : A -> Type} (f : forall a, B a) :
    Σ(f : A -> Σa, B a), pr1 o f == id.
  ⟨fun a => ⟨a, f a⟩, fun a => idp⟩

Definition pi_equiv_arrow_sigma_left.{u v} {A : Type.{u}} {B : A -> Type.{v}}
    (v : Σ(f : A -> Σa, B a), pr1 o f == id) (a : A) : B a.
  transport B (v.2 a) (v.1 a).2

  open funext
Definition pi_equiv_arrow_sigma {A : Type} (B : A -> Type) :
    (forall a, B a) <~> Σ(f : A -> Σa, B a), pr1 o f == id.
Proof.
    fapply equiv.MK,
    { exact pi_equiv_arrow_sigma_right},
    { exact pi_equiv_arrow_sigma_left},
    { intro v, induction v with f p, fapply sigma_eq: esimp,
      { apply eq_of_homotopy, intro a, fapply sigma_eq: esimp,
        { exact (p a)^-1},
        { apply inverseo, apply pathover_tr}},
      { apply pi_pathover_constant, intro a, apply eq_pathover_constant_right,
        refine ap_compose (fun f => f a) _ _ @ph _,
        refine ap02 _ !compose_eq_of_homotopy @ph _,
        refine !ap_eq_apd10 @ph _,
        refine apd10 (right_inv apd10 _) a @ph _,
        esimp, refine !sigma_eq_pr1 @ph _, apply square_of_eq, exact (con_Vp _)^-1}},
    { intro a, reflexivity}
Defined.




Defined. pi



namespace pi

  (* pointed pi types *)
  open pointed

Definition pointed_pi [instance] {A : Type} (P : A -> Type) [H : forall x, pointed (P x)]
      : pointed (forall x, P x).
  pointed.mk (fun x => (point _))

Defined. pi
