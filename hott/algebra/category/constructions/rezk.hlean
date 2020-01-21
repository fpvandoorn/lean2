(*
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jakob von Raumer

The Rezk completion
*)

import hit.two_quotient types.trunc types.arrow algebra.category.functor.exponential_laws

open eq category equiv trunc_two_quotient is_trunc iso e_closure function pi trunctype

namespace rezk
  section

  universes l k
  parameters {A : Type.{l}} [C : precategory.{l k} A]
  include C

  inductive rezk_Q : forall (a b : A), e_closure iso a b -> e_closure iso a b -> Type.
  | comp_con : forall (a b c : A) (g : b ≅ c) (f : a ≅ b) , rezk_Q [f @i g] ([f] @r [g])

Definition rezk_carrier . trunc_two_quotient 1 iso rezk_Q

  local attribute rezk_carrier [reducible]
Definition is_trunc_rezk_carrier [instance] : is_trunc 1 rezk_carrier . _

  variables {a b c : A}
Definition elt (a : A) : rezk_carrier . incl0 a
Definition pth (f : a ≅ b) : elt a = elt b . incl1 f

Definition resp_comp (g : b ≅ c) (f : a ≅ b) : pth (f @i g) = pth f @ pth g.
  incl2 (rezk_Q.comp_con g f)

Definition resp_id (a : A) : pth (iso.refl a) = idp.
Proof.
    apply cancel_right (pth (iso.refl a)), refine _ @ (concat_1p _)^-1,
    refine !resp_comp^-1 @ _,
    apply ap pth, apply iso_eq, apply id_left,
Defined.

  protectedDefinition rec {P : rezk_carrier -> Type} [forall x, is_trunc 1 (P x)]
    (Pe : forall a, P (elt a)) (Pp : forall (a b) (f : a ≅ b), Pe a =[pth f] Pe b)
    (Pcomp : forall (a b c) (g : b ≅ c) (f : a ≅ b),
      change_path (resp_comp g f) (Pp (f @i g)) = Pp f @o Pp g)
    (x : rezk_carrier) : P x.
Proof.
    induction x,
    { apply Pe },
    { apply Pp },
    { induction q with a b c g f, apply Pcomp }
Defined.

  protectedDefinition rec_on {P : rezk_carrier -> Type} [forall x, is_trunc 1 (P x)]
    (x : rezk_carrier)
    (Pe : forall a, P (elt a)) (Pp : forall (a b) (f : a ≅ b), Pe a =[pth f] Pe b)
    (Pcomp : forall (a b c) (g : b ≅ c) (f : a ≅ b),
      change_path (resp_comp g f) (Pp (f @i g)) = Pp f @o Pp g) : P x.
  rec Pe Pp Pcomp x

  protectedDefinition set_rec {P : rezk_carrier -> Type} [forall x, is_set (P x)]
    (Pe : forall a, P (elt a)) (Pp : forall (a b) (f : a ≅ b), Pe a =[pth f] Pe b)
    (x : rezk_carrier) : P x.
  rec Pe Pp !center x

  protectedDefinition prop_rec {P : rezk_carrier -> Type} [forall x, is_prop (P x)]
    (Pe : forall a, P (elt a)) (x : rezk_carrier) : P x.
  rec Pe !center !center x

  protectedDefinition elim {P : Type} [is_trunc 1 P] (Pe : A -> P)
    (Pp : forall (a b) (f : a ≅ b), Pe a = Pe b)
    (Pcomp : forall (a b c) (g : b ≅ c) (f : a ≅ b), Pp (f @i g) = Pp f @ Pp g)
    (x : rezk_carrier) : P.
Proof.
    induction x,
    { exact Pe a },
    { exact Pp s },
    { induction q with a b c g f, exact Pcomp g f }
Defined.

  protectedDefinition elim_on {P : Type} [is_trunc 1 P] (x : rezk_carrier)
    (Pe : A -> P) (Pp : forall (a b) (f : a ≅ b), Pe a = Pe b)
    (Pcomp : forall (a b c) (g : b ≅ c) (f : a ≅ b), Pp (f @i g) = Pp f @ Pp g) : P.
  elim Pe Pp Pcomp x

  protectedDefinition set_elim {P : Type} [is_set P] (Pe : A -> P)
    (Pp : forall (a b) (f : a ≅ b), Pe a = Pe b) (x : rezk_carrier) : P.
  elim Pe Pp !center x

  protectedDefinition prop_elim {P : Type} [is_prop P] (Pe : A -> P)
    (x : rezk_carrier) : P.
  elim Pe !center !center x

Definition elim_pth {P : Type} [is_trunc 1 P] {Pe : A -> P} {Pp : forall (a b) (f : a ≅ b), Pe a = Pe b}
    (Pcomp : forall (a b c) (g : b ≅  c) (f : a ≅ b), Pp (f @i g) = Pp f @ Pp g) {a b : A} (f : a ≅ b) :
    ap (elim Pe Pp Pcomp) (pth f) = Pp f.
  !elim_incl1

  --TODO generalize this to arbitrary truncated two-quotients or not?
  protectedDefinition elim_set.{m} (Pe : A -> Set.{m}) (Pp : forall (a b) (f : a ≅ b), Pe a <~> Pe b)
    (Pcomp : forall (a b c) (g : b ≅ c) (f : a ≅ b) (x : Pe a), Pp (f @i g) x = Pp g (Pp f x))
    (x : rezk_carrier) : Set.{m}.
  elim Pe (fun a b f => tua (Pp f)) (fun a b c g f => ap tua (equiv_eq (Pcomp g f)) @ !tua_trans) x

  protectedDefinition elim_set_pt.{m} (Pe : A -> Set.{m}) (Pp : forall (a b) (f : a ≅ b), Pe a <~> Pe b)
    (Pcomp : forall (a b c) (g : b ≅ c) (f : a ≅ b) (x : Pe a), Pp (f @i g) x = Pp g (Pp f x))
    (a : A) : trunctype.carrier (rezk.elim_set Pe Pp Pcomp (elt a)) = Pe a.
  idp

  protectedDefinition elim_set_pth {Pe : A -> Set} {Pp : forall (a b) (f : a ≅ b), Pe a <~> Pe b}
    (Pcomp : forall (a b c) (g : b ≅ c) (f : a ≅ b) (x : Pe a), Pp (f @i g) x = Pp g (Pp f x))
    {a b : A} (f : a ≅ b) :
    transport (elim_set Pe Pp Pcomp) (pth f) = Pp f.
Proof.
    rewrite [tr_eq_cast_ap_fn, ↑elim_set, ▸*],
    rewrite [ap_compose' trunctype.carrier, elim_pth], apply tcast_tua_fn
Defined.

Defined.
Defined. rezk open rezk






          rezk.elim_set [unfold 6]

namespace rezk
  section
  universes l k
  parameters (A : Type.{l}) (C : precategory.{l k} A)

Definition rezk_hom_left_pt (a : A) (b : @rezk_carrier A C) : Set.{k}.
Proof.
    refine rezk.elim_set _ _ _ b,
    { clear b, intro b, exact trunctype.mk' 0 (hom a b) },
    { clear b, intro b b' f, apply equiv_postcompose (iso.to_hom f) },
    { clear b, intro b b' b'' f g x, apply !assoc^-1 }
Defined.

  privateDefinition pathover_rezk_hom_left_pt {a b c : A} (f : hom a b) (g : b ≅ c) :
    pathover (rezk_hom_left_pt a) f (pth g) ((to_hom g) o f).
Proof.
    apply pathover_of_tr_eq, apply @homotopy_of_eq _ _ _ (fun f => (to_hom g) o f),
    apply rezk.elim_set_pth,
Defined.

Definition rezk_hom_left_pth_1_trunc [instance] (a a' : A) (f : a ≅ a') :
    forall b, is_trunc 1 (carrier (rezk_hom_left_pt a b) <~> carrier (rezk_hom_left_pt a' b)).
  fun b => is_trunc_equiv _ _ _

Definition rezk_hom_left_pth (a a' : A) (f : a ≅ a') (b : rezk_carrier) :
    carrier (rezk_hom_left_pt a b) <~> carrier (rezk_hom_left_pt a' b).
Proof.
    --induction b using rezk.rec with b' b' b g, --why does this not work if it works below?
    refine @rezk.rec _ _ _ (rezk_hom_left_pth_1_trunc a a' f) _ _ _ b,
    intro b, apply equiv_precompose (to_hom f^-1ⁱ), --how do i unfold properly at this point?
    { intro b b' g, apply equiv_pathover, intro g' g'' H,
      refine !pathover_rezk_hom_left_pt @op _,
      refine !assoc @ ap (fun x => x o _) _,  refine eq_of_parallel_po_right _ H,
      apply pathover_rezk_hom_left_pt },
    intro b b' b'' g g', apply @is_prop.elim, apply is_trunc_pathover, apply is_trunc_equiv
Defined.

Definition rezk_hom [unfold 3 4] (a b : @rezk_carrier A C) : Set.{k}.
Proof.
    refine rezk.elim_set _ _ _ a,
    { clear a, intro a, exact rezk_hom_left_pt a b },
    { clear a, intro a a' f, apply rezk_hom_left_pth a a' f },
    { clear a, intro a a' a'' Ef Eg Rfg, induction b using rezk.rec,
      apply assoc, apply is_prop.elimo, apply is_set.elimo }
Defined.

  privateDefinition pathover_rezk_hom_left {a b c : A} (f : hom a c) (g : a ≅ b) :
    pathover (fun x => rezk_hom x (elt c)) f (pth g) (f o (to_hom g)^-1).
Proof.
    apply pathover_of_tr_eq, apply @homotopy_of_eq _ _ _ (fun f => f o (to_hom g)^-1),
    apply rezk.elim_set_pth,
Defined.

  privateDefinition pathover_rezk_hom_right {a b c : A} (f : hom a b) (g : b ≅ c) : --todo delete?
    pathover (rezk_hom (elt a)) f (pth g) ((to_hom g) o f).
Proof.
    apply pathover_rezk_hom_left_pt,
Defined.

  privateDefinition transport_rezk_hom_eq_comp {a c : A} (f : hom a a) (g : a ≅ c) :
    transport (fun x => rezk_hom x x) (pth g) f = (to_hom g) o f o (to_hom g)^-1.
Proof.
    apply concat, apply tr_diag_eq_tr_tr rezk_hom,
    apply concat, apply ap (fun x => _ # x),
     apply tr_eq_of_pathover, apply pathover_rezk_hom_left,
    apply tr_eq_of_pathover, apply pathover_rezk_hom_left_pt
Defined.

Definition rezk_id (a : @rezk_carrier A C) : rezk_hom a a.
Proof.
    induction a using rezk.rec,
    apply id,
    { apply pathover_of_tr_eq, refine !transport_rezk_hom_eq_comp @ _,
      refine (ap (fun x => to_hom f o x) !id_left) @ _, apply right_inverse },
    apply is_set.elimo
Defined.

Definition rezk_comp_pt_pt {c : rezk_carrier} {a b : A}
    (g : carrier (rezk_hom (elt b) c))
    (f : carrier (rezk_hom (elt a) (elt b))) : carrier (rezk_hom (elt a) c).
Proof.
    induction c using rezk.set_rec with c c c' ic,
    exact g o f,
    { apply arrow_pathover_left, intro d,
      apply concato !pathover_rezk_hom_left_pt, apply pathover_idp_of_eq,
      apply concat, apply assoc, apply ap (fun x => x o f),
      apply inverse, apply tr_eq_of_pathover, apply pathover_rezk_hom_left_pt },
Defined.

Definition rezk_comp_pt_pth {c : rezk_carrier} {a b b' : A} {ib : iso b b'} :
    pathover (fun b => carrier (rezk_hom b c) -> carrier (rezk_hom (elt a) b) -> carrier (rezk_hom (elt a) c))
      (fun g f => rezk_comp_pt_pt g f) (pth ib) (fun g f => rezk_comp_pt_pt g f).
Proof.
    apply arrow_pathover_left, intro x,
    apply arrow_pathover_left, intro y,
    induction c using rezk.set_rec with c c c' ic,
    {  apply pathover_of_eq, apply inverse,
      apply concat, apply ap (fun x => rezk_comp_pt_pt x _), apply tr_eq_of_pathover,
       apply pathover_rezk_hom_left,
      apply concat, apply ap (rezk_comp_pt_pt _), apply tr_eq_of_pathover,
       apply pathover_rezk_hom_left_pt,
      refine !assoc @ ap (fun x => x o y) _,
      refine !assoc^-1 @ _,
      refine ap (fun y => x o y) !iso.left_inverse @ _,
      apply id_right },
    apply @is_prop.elimo
Defined.

Definition rezk_comp {a b c : @rezk_carrier A C} (g : rezk_hom b c) (f : rezk_hom a b) :
    rezk_hom a c.
Proof.
    induction a using rezk.set_rec with a a a' ia,
    { induction b using rezk.set_rec with b b b' ib,
      apply rezk_comp_pt_pt g f, apply rezk_comp_pt_pth },
    { induction b using rezk.set_rec with b b b' ib,
      apply arrow_pathover_left, intro f,
      induction c using rezk.set_rec with c c c' ic,
      { apply concato, apply pathover_rezk_hom_left,
        apply pathover_idp_of_eq, refine !assoc^-1 @ ap (fun x => g o x) _^-1,
        apply tr_eq_of_pathover, apply pathover_rezk_hom_left },
      apply is_prop.elimo,
      apply is_prop.elimo }
Defined.

Definition is_set_rezk_hom [instance] (a b : @rezk_carrier A C) : is_set (rezk_hom a b).
  _

  protectedDefinition id_left {a b : @rezk_carrier A C} (f : rezk_hom a b) :
    rezk_comp (rezk_id b) f = f.
Proof.
    induction a using rezk.prop_rec with a a a' ia,
    induction b using rezk.prop_rec with b b b' ib,
    apply id_left,
Defined.

  protectedDefinition id_right {a b : @rezk_carrier A C} (f : rezk_hom a b) :
    rezk_comp f (rezk_id a) = f.
Proof.
    induction a using rezk.prop_rec with a a a' ia,
    induction b using rezk.prop_rec with b b b' ib,
    apply id_right,
Defined.

  protectedDefinition assoc {a b c d : @rezk_carrier A C} (h : rezk_hom c d)
    (g : rezk_hom b c) (f : rezk_hom a b) :
    rezk_comp h (rezk_comp g f) = rezk_comp (rezk_comp h g) f.
Proof.
    induction a using rezk.prop_rec with a a a' ia,
    induction b using rezk.prop_rec with b b b' ib,
    induction c using rezk.prop_rec with c c c' ic,
    induction d using rezk.prop_rec with d d d' id,
    apply assoc,
Defined.

Definition rezk_precategory [instance] : precategory (@rezk_carrier A C).
  precategory.mk rezk_hom @rezk_comp rezk_id @assoc @id_left @id_right

Defined.

Definition to_rezk_Precategory.{l k} : Precategory.{l k} -> Precategory.{(max l k) k}.
Proof.
    intro C, apply Precategory.mk (@rezk_carrier (Precategory.carrier C) C),
    apply rezk_precategory _ _,
Defined.

Definition rezk_functor (C : Precategory) : functor C (to_rezk_Precategory C).
Proof.
    fapply functor.mk => apply elt,
    { intro a b f, exact f },
    do 2 (intros; reflexivity)
Defined.

  section
  parameters {A : Type} [C : precategory A]
  include C

  protectedDefinition elt_iso_of_iso {a b : A} (f : a ≅ b) : elt a ≅ elt b.
Proof.
    fapply iso.mk, apply to_hom f, apply functor.preserve_is_iso (rezk_functor _)
Defined.

  protectedDefinition iso_of_elt_iso {a b : A} (f : elt a ≅ elt b) : a ≅ b.
Proof.
    cases f with f Hf, cases Hf with inv linv rinv,
    fapply iso.mk, exact f, fapply is_iso.mk, exact inv, exact linv, exact rinv
Defined.

  protectedDefinition iso_of_elt_iso_distrib {a b c : A} (f : elt a ≅ elt b) (g : elt b ≅ elt c) :
    iso_of_elt_iso (f @i g) = (iso_of_elt_iso f) @i (iso_of_elt_iso g).
Proof.
    cases g with g Hg, cases Hg with invg linvg rinvg,
    cases f with f Hf, cases Hf with invf linvf rinvf,
    reflexivity
Defined.

  protectedDefinition iso_equiv_elt_iso (a b : A) : (a ≅ b) <~> (elt a ≅ elt b).
Proof.
    fapply equiv.MK, apply elt_iso_of_iso, apply iso_of_elt_iso,
    { intro f, cases f with f Hf, cases Hf with inv linv rinv, fapply iso_eq, reflexivity },
    { intro f, fapply iso_eq, reflexivity }
Defined.

  privateDefinition hom_transport_eq_transport_hom {a b b' : @rezk_carrier A C} (f : a ≅ b)
    (p : b = b') : to_hom (transport (iso a) p f) = transport (fun x => hom _ _) p (to_hom f).
  by cases p; reflexivity

  privateDefinition hom_transport_eq_transport_hom' {a a' b : @rezk_carrier A C} (f : a ≅ b)
    (p : a = a') : to_hom (transport (fun x => iso x b) p f) = transport (fun x => hom _ _) p (to_hom f).
  by cases p; reflexivity

  privateDefinition pathover_iso_pth {a b b' : A} (f : elt a ≅ elt b)
    (ib : b ≅ b') : pathover (fun x => iso (elt a) x) f (pth ib) (f @i elt_iso_of_iso ib).
Proof.
    apply pathover_of_tr_eq, apply iso_eq,
    apply concat, apply hom_transport_eq_transport_hom,
    apply tr_eq_of_pathover, apply pathover_rezk_hom_right A C
Defined.

  privateDefinition pathover_iso_pth' {a a' b : A} (f : elt a ≅ elt b)
    (ia : a ≅ a') : pathover (fun x => iso x (elt b)) f (pth ia) (elt_iso_of_iso (iso.symm ia) @i f).
Proof.
    apply pathover_of_tr_eq, apply iso_eq,
    apply concat, apply hom_transport_eq_transport_hom',
    apply tr_eq_of_pathover, apply pathover_rezk_hom_left A C
Defined.

  privateDefinition eq_of_iso_pt {a : A} {b : @rezk_carrier A C} :
    elt a ≅ b -> elt a = b.
Proof.
    intro f,
    induction b using rezk.set_rec with b b b' ib,
    apply pth, apply iso_of_elt_iso f,
    apply arrow_pathover, intro f g p, apply eq_pathover,
    refine (ap_pp _ _ _)stant @ph _ @hp !ap_id^-1, apply square_of_eq,
    refine !resp_comp^-1 @ (ap pth _)^-1 @ (concat_1p _)^-1,
    apply concat, apply inverse, apply ap rezk.iso_of_elt_iso,
    apply eq_of_parallel_po_right (pathover_iso_pth _ _) p,
    apply concat, apply iso_of_elt_iso_distrib,
    apply ap (fun x => _ @i x), apply equiv.to_left_inv !iso_equiv_elt_iso
Defined.

  protectedDefinition eq_of_iso {a b : @rezk_carrier A C} :
    a ≅ b -> a = b.
Proof.
    intro f,
    induction a using rezk.set_rec with a a a' ia,
    apply eq_of_iso_pt f,
    { induction b using rezk.set_rec with b b b' ib,
      { apply arrow_pathover, intro f g p, apply eq_pathover,
        refine !ap_id @ph _ @hp (ap_pp _ _ _)stant^-1, apply square_of_eq,
        refine (ap pth _) @ !resp_comp,
        assert H : g = (elt_iso_of_iso (iso.symm ia) @i f),
        apply eq_of_parallel_po_right p (pathover_iso_pth' _ _),
        rewrite H, apply inverse,
        apply concat, apply ap (fun x => ia @i x), apply iso_of_elt_iso_distrib,
        apply concat, apply ap (fun x => _ @i (x @i _)), apply equiv.to_left_inv !iso_equiv_elt_iso,
        apply iso_eq, apply inverse_comp_cancel_right },
       apply @is_prop.elimo }
Defined.

  protectedDefinition eq_of_iso_of_eq (a b : @rezk_carrier A C) (p : a = b) :
    eq_of_iso (iso_of_eq p) = p.
Proof.
    cases p, clear b,
    induction a using rezk.prop_rec,
    refine ap pth _ @ !resp_id,
    apply iso_eq, reflexivity
Defined.

  protectedDefinition iso_of_eq_of_iso (a b : @rezk_carrier A C) (f : a ≅ b) :
    iso_of_eq (eq_of_iso f) = f.
Proof.
    induction a using rezk.prop_rec with a,
    induction b using rezk.prop_rec with b,
    cases f with f Hf, apply iso_eq,
    apply concat, apply ap to_hom, apply !transport_iso_of_eq^-1,
    apply concat, apply ap to_hom, apply tr_eq_of_pathover, apply pathover_iso_pth,
    cases Hf with invf linv rinv, apply id_right,
Defined.

Defined.

Definition rezk_category.{l k} {A : Type.{l}} [C : precategory.{l k} A] :
    category.{(max l k) k} (@rezk_carrier.{l k} A C).
Proof.
    fapply category.mk (rezk_precategory A C),
    intros, fapply is_equiv.adjointify,
    apply rezk.eq_of_iso,
    apply rezk.iso_of_eq_of_iso,
    apply rezk.eq_of_iso_of_eq
Defined.

  section
  variable (C : Precategory)

Definition fully_faithful_rezk_functor : fully_faithful (rezk_functor C).
  by intros; apply is_equiv.is_equiv_id

  open trunc
Definition essentially_surj_rezk_functor : essentially_surjective (rezk_functor C).
Proof.
    intro a, esimp[to_rezk_Precategory] at *,
    induction a using rezk.prop_rec with a, apply tr,
    constructor, apply iso.refl (elt a),
Defined.

Definition is_weak_equiv_rezk_functor : is_weak_equivalence (rezk_functor C).
  prod.mk (fully_faithful_rezk_functor C) (essentially_surj_rezk_functor C)

Defined.

Defined. rezk
