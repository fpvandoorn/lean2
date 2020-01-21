(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz

Declaration of suspension
*)

import hit.pushout types.pointed2 cubical.square .connectedness

open pushout unit eq equiv pointed is_equiv

Definition susp' (A : Type) : Type . pushout (fun (a : A) => star) (fun (a : A) => star)

namespace susp

Definition north' {A : Type} : susp' A.
  inl star

Definition pointed_susp [instance] (X : Type)
    : pointed (susp' X).
  pointed.mk north'

Defined. susp open susp

Definition susp (X : Type) : pType.
pointed.MK (susp' X) north'

notation `⅀` . susp

namespace susp
  variable {A : Type}

Definition north {A : Type} : susp A.
  north'

Definition south {A : Type} : susp A.
  inr star

Definition merid (a : A) : @north A = @south A.
  glue a

  protectedDefinition rec {P : susp A -> Type} (PN : P north) (PS : P south)
    (Pm : forall (a : A), PN =[merid a] PS) (x : susp' A) : P x.
Proof.
    induction x with u u,
    { cases u, exact PN},
    { cases u, exact PS},
    { apply Pm},
Defined.

  protectedDefinition rec_on {P : susp A -> Type} (y : susp' A)
    (PN : P north) (PS : P south) (Pm : forall (a : A), PN =[merid a] PS) : P y.
  susp.rec PN PS Pm y

Definition rec_merid {P : susp A -> Type} (PN : P north) (PS : P south)
    (Pm : forall (a : A), PN =[merid a] PS) (a : A)
      : apd (susp.rec PN PS Pm) (merid a) = Pm a.
  !rec_glue

  protectedDefinition elim {P : Type} (PN : P) (PS : P) (Pm : A -> PN = PS)
    (x : susp' A) : P.
  susp.rec PN PS (fun a => pathover_of_eq _ (Pm a)) x

  protectedDefinition elim_on {P : Type} (x : susp' A)
    (PN : P) (PS : P)  (Pm : A -> PN = PS) : P.
  susp.elim PN PS Pm x

Definition elim_merid {P : Type} {PN PS : P} (Pm : A -> PN = PS) (a : A)
    : ap (susp.elim PN PS Pm) (merid a) = Pm a.
Proof.
    apply eq_of_fn_eq_fn_inv !(pathover_constant (merid a)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑susp.elim,rec_merid],
Defined.

  protectedDefinition elim_type (PN : Type) (PS : Type) (Pm : A -> PN <~> PS)
    (x : susp' A) : Type.
  pushout.elim_type (fun x => PN) (fun x => PS) Pm x

  protectedDefinition elim_type_on (x : susp' A)
    (PN : Type) (PS : Type)  (Pm : A -> PN <~> PS) : Type.
  susp.elim_type PN PS Pm x

Definition elim_type_merid (PN : Type) (PS : Type) (Pm : A -> PN <~> PS)
    (a : A) : transport (susp.elim_type PN PS Pm) (merid a) = Pm a.
  !elim_type_glue

Definition elim_type_merid_inv {A : Type} (PN : Type) (PS : Type) (Pm : A -> PN <~> PS)
    (a : A) : transport (susp.elim_type PN PS Pm) (merid a)^-1 = to_inv (Pm a).
  !elim_type_glue_inv

  protectedDefinition merid_square {a a' : A} (p : a = a')
    : square (merid a) (merid a') idp idp.
  by cases p; apply vrefl

Defined. susp







namespace susp

  open is_trunc is_conn trunc

  (* Theorem 8.2.1 *)
Definition is_conn_susp [instance] (n : trunc_index) (A : Type)
    [H : is_conn n A] : is_conn (n .+1) (susp A).
  is_contr.mk (tr north)
Proof.
    intro x, induction x with x, induction x,
    { reflexivity },
    { exact (trunc.rec (fun a => ap tr (merid a)) (center (trunc n A))) },
    { generalize (center (trunc n A)),
      intro x, induction x with a',
      apply pathover_of_tr_eq,
      rewrite [eq_transport_Fr,idp_con],
      revert H, induction n with n IH: intro H,
      { apply is_prop.elim },
      { change ap (@tr n .+2 (susp A)) (merid a) = ap tr (merid a'),
        generalize a',
        apply is_conn_fun.elim n
              (is_conn_fun_from_unit n A a)
              (fun x : A => trunctype.mk' n (ap (@tr n .+2 (susp A)) (merid a) = ap tr (merid x))),
        intros,
        change ap (@tr n .+2 (susp A)) (merid a) = ap tr (merid a),
        reflexivity }
    }
Defined.

  (* Flattening lemma *)

  open prod prod.ops
  section
    universe variable u
    parameters (A : Type) (PN PS : Type.{u}) (Pm : A -> PN <~> PS)
    include Pm

    local abbreviation P . susp.elim_type PN PS Pm

    local abbreviation F : A \* PN -> PN . fun z => z.2

    local abbreviation G : A \* PN -> PS . fun z => Pm z.1 z.2

    protectedDefinition flattening : sigma P <~> pushout F G.
    begin
      apply equiv.trans !pushout.flattening,
      fapply pushout.equiv,
      { exact sigma.equiv_prod A PN },
      { apply sigma.sigma_unit_left },
      { apply sigma.sigma_unit_left },
      { reflexivity },
      { reflexivity }
    end
Defined.

Defined. susp

(* Functoriality and equivalence *)
namespace susp
  variables {A B : Type} (f : A -> B)
  include f

Definition susp_functor' : susp A -> susp B.
Proof.
    intro x, induction x with a,
    { exact north },
    { exact south },
    { exact merid (f a) }
Defined.

  variable [Hf : is_equiv f]
  include Hf

  open is_equiv
  protectedDefinition is_equiv_functor [instance] : is_equiv (susp_functor' f).
  adjointify (susp_functor' f) (susp_functor' f^-1)
  abstract begin
    intro sb, induction sb with b, do 2 reflexivity,
    apply eq_pathover,
    rewrite [ap_id,ap_compose' (susp_functor' f) (susp_functor' f^-1)] =>
    krewrite [susp.elim_merid,susp.elim_merid], apply transpose,
    apply susp.merid_square (right_inv f b)
Defined. end
  abstract begin
    intro sa, induction sa with a, do 2 reflexivity,
    apply eq_pathover,
    rewrite [ap_id,ap_compose' (susp_functor' f^-1) (susp_functor' f)] =>
    krewrite [susp.elim_merid,susp.elim_merid], apply transpose,
    apply susp.merid_square (left_inv f a)
Defined. end


Defined. susp

namespace susp
  variables {A B : Type} (f : A <~> B)

  protectedDefinition equiv : susp A <~> susp B.
  equiv.mk (susp_functor' f) _
Defined. susp

namespace susp
  open pointed is_trunc
  variables {X X' Y Y' Z : pType}

Definition susp_functor (f : X ->* Y) : susp X ->* susp Y.
Proof.
    fconstructor,
    { exact susp_functor' f } =>
    { reflexivity }
Defined.

Definition is_equiv_susp_functor (f : X ->* Y) [Hf : is_equiv f]
    : is_equiv (susp_functor f).
  susp.is_equiv_functor f

Definition susp_pequiv (f : X <~>* Y) : susp X <~>* susp Y.
  pequiv_of_equiv (susp.equiv f) idp

Definition susp_functor_pcompose (g : Y ->* Z) (f : X ->* Y) :
    susp_functor (g o* f) ==* susp_functor g o* susp_functor f.
Proof.
    fapply Build_pHomotopy,
    { intro x, induction x,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        refine !elim_merid @ _ @ (ap_compose (susp_functor g) _ _)^-1ᵖ =>
        refine _ @ ap02 _ !elim_merid^-1, exact !elim_merid^-1 }},
    { reflexivity },
Defined.

Definition susp_functor_phomotopy {f g : X ->* Y} (p : f ==* g) :
    susp_functor f ==* susp_functor g.
Proof.
    fapply Build_pHomotopy,
    { intro x, induction x,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover, apply hdeg_square, esimp, refine !elim_merid @ _ @ !elim_merid^-1ᵖ,
        exact ap merid (p a), }},
    { reflexivity },
Defined.

Definition susp_functor_pid (A : pType) : susp_functor (pid A) ==* pid (susp A).
Proof.
    fapply Build_pHomotopy,
    { intro x, induction x,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square, apply elim_merid }},
    { reflexivity },
Defined.

  (* adjunction originally  ported from Coq-HoTT,
     but we proved some additional naturality conditions *)

Definition loop_susp_unit (X : pType) : X ->* Ω(susp X).
Proof.
    fconstructor,
    { intro x, exact merid x @ (merid (point _))^-1 },
    { apply con.right_inv },
Defined.

Definition loop_susp_unit_natural (f : X ->* Y)
    : loop_susp_unit Y o* f ==* Ω-> (susp_functor f) o* loop_susp_unit X.
Proof.
    induction X with X x, induction Y with Y y, induction f with f pf, esimp at *, induction pf,
    fapply Build_pHomotopy,
    { intro x', symmetry,
      exact
        !ap1_gen_idp_left @
        ((ap_pp _ _ _) @
        whisker_left _ !ap_inv) @
        (!elim_merid ◾ (inverse2 !elim_merid)) },
    { rewrite [▸*, idp_con (con.right_inv _)],
      apply inv_con_eq_of_eq_con,
      refine _ @ (concat_pp_p _ _ _)',
      rewrite inverse2_right_inv,
      refine _ @ (concat_pp_p _ _ _)',
      rewrite [ap_con_right_inv],
      rewrite [ap1_gen_idp_left_con],
      rewrite [-ap_compose (concat idp)] },
Defined.

Definition loop_susp_counit (X : pType) : susp (loops X) ->* X.
Proof.
    fapply Build_pMap,
    { intro x, induction x, exact (point _), exact (point _), exact a },
    { reflexivity },
Defined.

Definition loop_susp_counit_natural (f : X ->* Y)
    : f o* loop_susp_counit X ==* loop_susp_counit Y o* (susp_functor (ap1 f)).
Proof.
    induction X with X x, induction Y with Y y, induction f with f pf, esimp at *, induction pf,
    fconstructor,
    { intro x', induction x' with p,
       { reflexivity },
      { reflexivity },
      { esimp, apply eq_pathover, apply hdeg_square,
        xrewrite [ap_compose' f, ap_compose' (susp.elim (f x) (f x) (fun (a : f x = f x) => a)),▸*],
        xrewrite [+elim_merid, ap1_gen_idp_left] }},
    { reflexivity }
Defined.

Definition loop_susp_counit_unit (X : pType)
    : ap1 (loop_susp_counit X) o* loop_susp_unit (loops X) ==* pid (loops X).
Proof.
    induction X with X x, fconstructor,
    { intro p, esimp,
      refine !ap1_gen_idp_left @
             ((ap_pp _ _ _) @
             whisker_left _ !ap_inv) @
             (!elim_merid ◾ inverse2 !elim_merid) },
    { rewrite [▸*,inverse2_right_inv (elim_merid id idp)],
      refine (concat_pp_p _ _ _) @ _,
      xrewrite [ap_con_right_inv (susp.elim x x (fun a => a)) (merid idp),ap1_gen_idp_left_con,
        -ap_compose] }
Defined.

Definition loop_susp_unit_counit (X : pType)
    : loop_susp_counit (susp X) o* susp_functor (loop_susp_unit X) ==* pid (susp X).
Proof.
    induction X with X x, fconstructor,
    { intro x', induction x',
      { reflexivity },
      { exact merid (point _) },
      { apply eq_pathover,
        xrewrite [▸*, ap_id, ap_compose' (susp.elim north north (fun a => a)), +elim_merid,▸*],
        apply square_of_eq, exact (concat_1p _) @ !inv_con_cancel_right^-1 }},
    { reflexivity }
Defined.

Definition susp_elim {X Y : pType} (f : X ->* loops Y) : susp X ->* Y.
  loop_susp_counit Y o* susp_functor f

Definition loop_susp_intro {X Y : pType} (f : susp X ->* Y) : X ->* loops Y.
  ap1 f o* loop_susp_unit X

Definition susp_elim_susp_functor {A B C : pType} (g : B ->* loops C) (f : A ->* B) :
    susp_elim g o* susp_functor f ==* susp_elim (g o* f).
Proof.
    refine !passoc @* _, exact pwhisker_left _ !susp_functor_pcompose^-1*
Defined.

Definition susp_elim_phomotopy {A B : pType} {f g : A ->* loops B} (p : f ==* g) : susp_elim f ==* susp_elim g.
  pwhisker_left _ (susp_functor_phomotopy p)

Definition susp_elim_natural {X Y Z : pType} (g : Y ->* Z) (f : X ->* loops Y)
    : g o* susp_elim f ==* susp_elim (Ω-> g o* f).
Proof.
    refine _ @* pwhisker_left _ !susp_functor_pcompose^-1* =>
    refine !passoc^-1* @* _ @* !passoc,
    exact pwhisker_right _ !loop_susp_counit_natural
Defined.

Definition loop_susp_intro_natural {X Y Z : pType} (g : susp Y ->* Z) (f : X ->* Y) :
    loop_susp_intro (g o* susp_functor f) ==* loop_susp_intro g o* f.
  pwhisker_right _ !ap1_pcompose @* !passoc @* pwhisker_left _ !loop_susp_unit_natural^-1* @*
  !passoc^-1*

Definition susp_adjoint_loop_right_inv {X Y : pType} (g : X ->* loops Y) :
    loop_susp_intro (susp_elim g) ==* g.
Proof.
    refine !pwhisker_right !ap1_pcompose @* _,
    refine !passoc @* _,
    refine !pwhisker_left !loop_susp_unit_natural^-1* @* _,
    refine !passoc^-1* @* _,
    refine !pwhisker_right !loop_susp_counit_unit @* _,
    apply pid_pcompose
Defined.

Definition susp_adjoint_loop_left_inv {X Y : pType} (f : susp X ->* Y) :
    susp_elim (loop_susp_intro f) ==* f.
Proof.
    refine !pwhisker_left !susp_functor_pcompose @* _ =>
    refine !passoc^-1* @* _,
    refine !pwhisker_right !loop_susp_counit_natural^-1* @* _,
    refine !passoc @* _,
    refine !pwhisker_left !loop_susp_unit_counit @* _,
    apply pcompose_pid
Defined.

Definition susp_adjoint_loop_unpointed (X Y : pType) : susp X ->* Y <~> X ->* loops Y.
Proof.
    fapply equiv.MK,
    { exact loop_susp_intro },
    { exact susp_elim },
    { intro g, apply path_pforall, exact susp_adjoint_loop_right_inv g },
    { intro f, apply path_pforall, exact susp_adjoint_loop_left_inv f }
Defined.

Definition susp_functor_pconst_homotopy {X Y : pType} (x : susp X) :
    susp_functor (pconst X Y) x = (point _).
Proof.
    induction x,
    { reflexivity },
    { exact (merid (point _))^-1 },
    { apply eq_pathover, refine !elim_merid @ph _ @hp (ap_pp _ _ _)stant^-1, exact square_of_eq (con_pV _)^-1 }
Defined.

Definition susp_functor_pconst (X Y : pType) : susp_functor (pconst X Y) ==* pconst (susp X) (susp Y).
Proof.
    fapply Build_pHomotopy,
    { exact susp_functor_pconst_homotopy } =>
    { reflexivity }
Defined.

Definition susp_pfunctor (X Y : pType) : ppMap X Y ->* ppMap (susp X) (susp Y).
  Build_pMap susp_functor (path_pforall !susp_functor_pconst)

Definition susp_pelim (X Y : pType) : ppMap X (loops Y) ->* ppMap (susp X) Y.
  ppcompose_left (loop_susp_counit Y) o* susp_pfunctor X (loops Y)

Definition loop_susp_pintro (X Y : pType) : ppMap (susp X) Y ->* ppMap X (loops Y).
  ppcompose_right (loop_susp_unit X) o* pap1 (susp X) Y

Definition loop_susp_pintro_natural_left (f : X' ->* X) :
    psquare (loop_susp_pintro X Y) (loop_susp_pintro X' Y)
            (ppcompose_right (susp_functor f)) (ppcompose_right f).
  !pap1_natural_left @h* ppcompose_right_psquare (loop_susp_unit_natural f)^-1*

Definition loop_susp_pintro_natural_right (f : Y ->* Y') :
    psquare (loop_susp_pintro X Y) (loop_susp_pintro X Y')
            (ppcompose_left f) (ppcompose_left (Ω-> f)).
  !pap1_natural_right @h* !ppcompose_left_ppcompose_right^-1*

Definition is_equiv_loop_susp_pintro (X Y : pType) :
    is_equiv (loop_susp_pintro X Y).
Proof.
    fapply adjointify,
    { exact susp_pelim X Y },
    { intro g, apply path_pforall, exact susp_adjoint_loop_right_inv g },
    { intro f, apply path_pforall, exact susp_adjoint_loop_left_inv f }
Defined.

Definition susp_adjoint_loop (X Y : pType) : ppMap (susp X) Y <~>* ppMap X (loops Y).
  pequiv_of_pmap (loop_susp_pintro X Y) (is_equiv_loop_susp_pintro X Y)

Definition susp_adjoint_loop_natural_right (f : Y ->* Y') :
    psquare (susp_adjoint_loop X Y) (susp_adjoint_loop X Y')
            (ppcompose_left f) (ppcompose_left (Ω-> f)).
  loop_susp_pintro_natural_right f

Definition susp_adjoint_loop_natural_left (f : X' ->* X) :
    psquare (susp_adjoint_loop X Y) (susp_adjoint_loop X' Y)
            (ppcompose_right (susp_functor f)) (ppcompose_right f).
  loop_susp_pintro_natural_left f

Definition ap1_susp_elim {A : pType} {X : pType} (p : A ->* loops X) :
    Ω->(susp_elim p) o* loop_susp_unit A ==* p.
  susp_adjoint_loop_right_inv p

  (* the underlying homotopies of susp_adjoint_loop_natural_* *)
Definition susp_adjoint_loop_nat_right (f : susp X ->* Y) (g : Y ->* Z)
    : susp_adjoint_loop X Z (g o* f) ==* ap1 g o* susp_adjoint_loop X Y f.
Proof.
    esimp [susp_adjoint_loop],
    refine _ @* !passoc,
    apply pwhisker_right,
    apply ap1_pcompose
Defined.

Definition susp_adjoint_loop_nat_left (f : Y ->* loops Z) (g : X ->* Y)
    : (susp_adjoint_loop X Z)^-1ᵉ (f o* g) ==* (susp_adjoint_loop Y Z)^-1ᵉ f o* susp_functor g.
Proof.
    esimp [susp_adjoint_loop],
    refine _ @* !passoc^-1*,
    apply pwhisker_left,
    apply susp_functor_pcompose
Defined.

  (* iterated suspension *)
Definition iterate_susp (n : ℕ) (A : pType) : pType . iterate (fun X => susp X) n A

  open is_conn trunc_index nat
Definition iterate_susp_succ (n : ℕ) (A : pType) :
    iterate_susp (succ n) A = susp (iterate_susp n A).
  idp

Definition is_conn_iterate_susp [instance] (n : ℕ₋₂) (m : ℕ) (A : pType)
    [H : is_conn n A] : is_conn (n + m) (iterate_susp m A).
Proof. induction m with m IH, exact H, exact @is_conn_susp _ _ IH end

  (* Separate cases for n = 0, which comes up often *)
Definition is_conn_iterate_susp_zero [instance] (m : ℕ) (A : pType)
    [H : is_conn 0 A] : is_conn m (iterate_susp m A).
Proof. induction m with m IH, exact H, exact @is_conn_susp _ _ IH end

Definition iterate_susp_functor (n : ℕ) {A B : pType} (f : A ->* B) :
    iterate_susp n A ->* iterate_susp n B.
Proof.
    induction n with n g,
    { exact f },
    { exact susp_functor g }
Defined.

Definition iterate_susp_succ_in (n : ℕ) (A : pType) :
    iterate_susp (succ n) A <~>* iterate_susp n (susp A).
Proof.
    induction n with n IH,
    { reflexivity},
    { exact susp_pequiv IH}
Defined.

Definition iterate_susp_adjoint_loopn (X Y : pType) (n : ℕ) :
    ppMap (iterate_susp n X) Y <~>* ppMap X (Ω[n] Y).
Proof.
    revert X Y, induction n with n IH: intro X Y,
    { reflexivity },
    { refine !susp_adjoint_loop @e* !IH @e* _, apply pequiv_ppcompose_left,
      symmetry, apply loopn_succ_in }
Defined.

Defined. susp
