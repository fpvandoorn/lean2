(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
*)
import types.trunc types.pi arity

open eq is_trunc pi equiv

namespace category

(*
  Just as in Coq-HoTT we add two redundant fields to precategories: assoc' and id_id.
  The first is to make (Cᵒᵖ)ᵒᵖ = CDefinitionally when C is a constructor.
  The second is to ensure that the functor from the terminal category 1 ⇒ Cᵒᵖ is
    opposite to the functor 1 ⇒ C.
*)

  structure precategory [class] (ob : Type) : Type.
  mk' ::
    (hom : ob -> ob -> Type)
    (comp : forall (a b c : ob), hom b c -> hom a b -> hom a c)
    (ID : forall (a : ob), hom a a)
    (assoc  : forall (a b c d : ob) (h : hom c d) (g : hom b c) (f : hom a b),
       comp h (comp g f) = comp (comp h g) f)
    (assoc' : forall (a b c d : ob) (h : hom c d) (g : hom b c) (f : hom a b),
       comp (comp h g) f = comp h (comp g f))
    (id_left : forall (a b : ob) (f : hom a b), comp !ID f = f)
    (id_right : forall (a b : ob) (f : hom a b), comp f !ID = f)
    (id_id : forall (a : ob), comp !ID !ID = ID a)
    (is_set_hom : forall (a b : ob), is_set (hom a b))

  attribute precategory.is_set_hom [instance]

  infixr o . precategory.comp
  (* input ⟶ using \--> (this is a different arrow than \-> (->)) *)
  infixl [parsing_only] ` ⟶ `:60 . precategory.hom
  namespace hom
    infixl ` ⟶ `:60 . precategory.hom (* if you open this namespace, hom a b is printed as a ⟶ b *)
Defined. hom

  abbreviation hom         . @precategory.hom
  abbreviation comp        . @precategory.comp
  abbreviation ID          . @precategory.ID
  abbreviation assoc       . @precategory.assoc
  abbreviation assoc'      . @precategory.assoc'
  abbreviation id_left     . @precategory.id_left
  abbreviation id_right    . @precategory.id_right
  abbreviation id_id       . @precategory.id_id
  abbreviation is_set_hom . @precategory.is_set_hom

Definition is_prop_hom_eq {ob : Type} [C : precategory ob] {x y : ob} (f g : x ⟶ y)
    : is_prop (f = g).
  _

  (* the constructor you want to use in practice *)
  protectedDefinition precategory.mk {ob : Type} (hom : ob -> ob -> Type)
    [set : forall (a b : ob), is_set (hom a b)]
    (comp : forall (a b c : ob), hom b c -> hom a b -> hom a c) (ID : forall (a : ob), hom a a)
    (ass : forall (a b c d : ob) (h : hom c d) (g : hom b c) (f : hom a b),
       comp h (comp g f) = comp (comp h g) f)
    (idl : forall (a b : ob) (f : hom a b), comp (ID b) f = f)
    (idr : forall (a b : ob) (f : hom a b), comp f (ID a) = f) : precategory ob.
  precategory.mk' hom comp ID ass (fun a b c d h g f => !ass^-1) idl idr (fun a => !idl) set

  section basic_lemmas
    variables {ob : Type} [C : precategory ob]
    variables {a b c d : ob} {h : c ⟶ d} {g g' : hom b c} {f f' : hom a b} {i : a ⟶ a}
    include C

Definition id . ID a

Definition id_leftright       (f : hom a b) : id o f o id = f . !id_left @ !id_right
Definition comp_id_eq_id_comp (f : hom a b) : f o id = id o f . !id_right @ !id_left^-1
Definition id_comp_eq_comp_id (f : hom a b) : id o f = f o id . !id_left @ !id_right^-1

Definition hom_whisker_left (g : b ⟶ c) (p : f = f') : g o f = g o f'.
    ap (fun x => g o x) p

Definition hom_whisker_right (g : c ⟶ a) (p : f = f') : f o g = f' o g.
    ap (fun x => x o g) p

    (* many variants of hom_pathover are defined in .iso and .functor.basic *)

Definition left_id_unique (H : forall {b} {f : hom b a}, i o f = f) : i = id.
    calc i = i o id : by rewrite id_right
       ... = id     : by rewrite H

Definition right_id_unique (H : forall {b} {f : hom a b}, f o i = f) : i = id.
    calc i = id o i : by rewrite id_left
       ... = id     : by rewrite H

Definition homset (x y : ob) : Set.
    Set.mk (hom x y) _

Definition comp2 (p : g = g') (q : f = f') : g o f = g' o f'.
    ap011 (fun g f => comp g f) p q

    infix ` o2 `:79 . comp2
Defined. basic_lemmas
  section squares
    parameters {ob : Type} [C : precategory ob]
    local infixl ` ⟶ `:25 . @precategory.hom ob C
    local infixr o    . @precategory.comp ob C _ _ _
Definition compose_squares {xa xb xc ya yb yc : ob}
      {xg : xb ⟶ xc} {xf : xa ⟶ xb} {yg : yb ⟶ yc} {yf : ya ⟶ yb}
      {wa : xa ⟶ ya} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (xyab : wb o xf = yf o wa) (xybc : wc o xg = yg o wb)
        : wc o (xg o xf) = (yg o yf) o wa.
    calc
      wc o (xg o xf) = (wc o xg) o xf : by rewrite assoc
        ... = (yg o wb) o xf : by rewrite xybc
        ... = yg o (wb o xf) : by rewrite assoc
        ... = yg o (yf o wa) : by rewrite xyab
        ... = (yg o yf) o wa : by rewrite assoc

Definition compose_squares_2x2 {xa xb xc ya yb yc za zb zc : ob}
      {xg : xb ⟶ xc} {xf : xa ⟶ xb} {yg : yb ⟶ yc} {yf : ya ⟶ yb} {zg : zb ⟶ zc} {zf : za ⟶ zb}
      {va : ya ⟶ za} {vb : yb ⟶ zb} {vc : yc ⟶ zc} {wa : xa ⟶ ya} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (xyab : wb o xf = yf o wa) (xybc : wc o xg = yg o wb)
      (yzab : vb o yf = zf o va) (yzbc : vc o yg = zg o vb)
        : (vc o wc) o (xg o xf) = (zg o zf) o (va o wa).
    calc
      (vc o wc) o (xg o xf) = vc o (wc o (xg o xf)) : by rewrite (assoc vc wc _)
        ... = vc o ((yg o yf) o wa) : by rewrite (compose_squares xyab xybc)
        ... = (vc o (yg o yf)) o wa : by rewrite assoc
        ... = ((zg o zf) o va) o wa : by rewrite (compose_squares yzab yzbc)
        ... = (zg o zf) o (va o wa) : by rewrite assoc

Definition square_precompose {xa xb xc yb yc : ob}
      {xg : xb ⟶ xc} {yg : yb ⟶ yc} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (H : wc o xg = yg o wb) (xf : xa ⟶ xb) : wc o xg o xf = yg o wb o xf.
    calc
      wc o xg o xf = (wc o xg) o xf : by rewrite assoc
        ... = (yg o wb) o xf        : by rewrite H
        ... = yg o wb o xf          : by rewrite assoc

Definition square_postcompose {xb xc yb yc yd : ob}
      {xg : xb ⟶ xc} {yg : yb ⟶ yc} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (H : wc o xg = yg o wb) (yh : yc ⟶ yd) : (yh o wc) o xg = (yh o yg) o wb.
    calc
      (yh o wc) o xg = yh o wc o xg : by rewrite assoc
        ... = yh o yg o wb          : by rewrite H
        ... = (yh o yg) o wb        : by rewrite assoc

Definition square_prepostcompose {xa xb xc yb yc yd : ob}
      {xg : xb ⟶ xc} {yg : yb ⟶ yc} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (H : wc o xg = yg o wb) (yh : yc ⟶ yd) (xf : xa ⟶ xb)
        : (yh o wc) o (xg o xf) = (yh o yg) o (wb o xf) .
    square_precompose (square_postcompose H yh) xf

Defined. squares

  structure Precategory : Type.
    (carrier : Type)
    (struct : precategory carrier)

Definition precategory.Mk {ob} (C) : Precategory . Precategory.mk ob C
Definition precategory.MK (a b c d e f g h) : Precategory.
  Precategory.mk a (@precategory.mk a b c d e f g h)

  abbreviation carrier . @Precategory.carrier

  attribute Precategory.carrier [coercion]
  attribute Precategory.struct [instance] [priority 10000] [coercion]
  (*Definition precategory.carrier [coercion] . Precategory.carrier *)
  (*Definition precategory.struct [instance] [coercion] . Precategory.struct *)
  notation g ` o[`:60 C:0 `] `:0 f:60.
  @comp (Precategory.carrier C) (Precategory.struct C) _ _ _ g f
  (* TODO: make this left associative *)

Definition Precategory.eta (C : Precategory) : Precategory.mk C C = C.
  Precategory.rec (fun ob c => idp) C

  (*Characterization of paths between precategories*)
  (* introduction tule for paths between precategories *)

Definition precategory_eq {ob : Type}
    {C D : precategory ob}
    (p : forall {a b}, @hom ob C a b = @hom ob D a b)
    (q : forall a b c g f, cast p (@comp ob C a b c g f) = @comp ob D a b c (cast p g) (cast p f))
      : C = D.
Proof.
    induction C with hom1 c1 ID1 a b il ir, induction D with hom2 c2 ID2 a' b' il' ir',
    esimp at *,
    revert q, eapply homotopy2.rec_on @p, esimp, clear p, intro p q, induction p,
    esimp at *,
    have H : c1 = c2,
    begin apply eq_of_homotopy3, intros, apply eq_of_homotopy2, intros, apply q end,
    induction H,
    have K : ID1 = ID2,
    begin apply eq_of_homotopy, intro a, exact !ir'^-1 @ !il end,
    induction K,
    apply ap0111111 (precategory.mk' hom1 c1 ID1): apply is_prop.elim
Defined.


Definition precategory_eq_of_equiv {ob : Type}
    {C D : precategory ob}
    (p : forall (a b), @hom ob C a b <~> @hom ob D a b)
    (q : forall {a b c} g f, p (@comp ob C a b c g f) = @comp ob D a b c (p g) (p f))
      : C = D.
Proof.
    fapply precategory_eq,
    { intro a b, exact ua !@p},
    { intros, refine !cast_ua @ !q @ _, apply ap011 !@comp !cast_ua^-1 !cast_ua^-1},
Defined.

(* if we need to prove properties about precategory_eq, it might be easier with the following proof:
Proof.
    induction C with hom1 comp1 ID1, induction D with hom2 comp2 ID2, esimp at *,
    have H : Σ(s : hom1 = hom2), (fun a b => equiv_of_eq (apd100 s a b)) = p,
    begin
      fconstructor,
      { apply eq_of_homotopy2, intros, apply ua, apply p},
      { apply eq_of_homotopy2, intros, rewrite [to_right_inv !eq_equiv_homotopy2, equiv_of_eq_ua]}
    end,
    induction H with H1 H2, induction H1, esimp at H2,
    have K : (fun a b => equiv.refl) = p,
    begin refine _ @ H2, apply eq_of_homotopy2, intros, exact !equiv_of_eq_refl^-1 end,
    induction K, clear H2,
    esimp at *,
    have H : comp1 = comp2,
    begin apply eq_of_homotopy3, intros, apply eq_of_homotopy2, intros, apply q end,
    have K : ID1 = ID2,
    begin apply eq_of_homotopy, intros, apply r end,
    induction H, induction K,
    apply ap0111111 (precategory.mk' hom1 comp1 ID1): apply is_prop.elim
Defined.
*)

Definition Precategory_eq {C D : Precategory}
    (p : carrier C = carrier D)
    (q : forall {a b : C}, a ⟶ b = cast p a ⟶ cast p b)
    (r : forall {a b c : C} (g : b ⟶ c) (f : a ⟶ b), cast q (g o f) = cast q g o cast q f)
       : C = D.
Proof.
    induction C with X C, induction D with Y D, esimp at *, induction p,
    esimp at *,
    apply ap (Precategory.mk X),
    apply precategory_eq @q @r
Defined.

Definition Precategory_eq_of_equiv {C D : Precategory}
    (p : carrier C <~> carrier D)
    (q : forall (a b : C), a ⟶ b <~> p a ⟶ p b)
    (r : forall {a b c : C} (g : b ⟶ c) (f : a ⟶ b), q (g o f) = q g o q f)
       : C = D.
Proof.
    induction C with X C, induction D with Y D, esimp at *,
    revert q r, eapply equiv.rec_on_ua p, clear p, intro p, induction p, esimp,
    intros,
    apply ap (Precategory.mk X),
    apply precategory_eq_of_equiv @q @r
Defined.

  (* elimination rules for paths between precategories. *)
  (* The first elimination rule is "ap carrier" *)

Definition Precategory_eq_hom {C D : Precategory} (p : C = D) (a b : C)
    : hom a b = hom (cast (ap carrier p) a) (cast (ap carrier p) b).
  by induction p; reflexivity
  --(ap10 (ap10 (apdt (fun x => @hom (carrier x) (Precategory.struct x)) p^-1ᵖ) a) b)^-1ᵖ @ _


  (* beta/eta rules *)
Definition ap_Precategory_eq' {C D : Precategory}
    (p : carrier C = carrier D)
    (q : forall {a b : C}, a ⟶ b = cast p a ⟶ cast p b)
    (r : forall {a b c : C} (g : b ⟶ c) (f : a ⟶ b), cast q (g o f) = cast q g o cast q f)
    (s : forall a, cast q (ID a) = ID (cast p a)) : ap carrier (Precategory_eq p @q @r) = p.
Proof.
    induction C with X C, induction D with Y D, esimp at *, induction p,
    rewrite [↑Precategory_eq, -ap_compose,↑function.compose =>ap_constant]
Defined.

  (*
Definition Precategory_eq'_eta {C D : Precategory} (p : C = D) :
    Precategory_eq
      (ap carrier p)
      (Precategory_eq_hom p)
      (by induction p; intros; reflexivity) = p.
Proof.
    induction p, induction C with X C, unfold Precategory_eq,
    induction C, unfold precategory_eq, exact sorry
Defined.
  *)

(*
Definition Precategory_eq2 {C D : Precategory} (p q : C = D)
    (r : ap carrier p = ap carrier q)
    (s : Precategory_eq_hom p =[r] Precategory_eq_hom q)
      : p = q.
Proof.

Defined.
*)

Defined. category
