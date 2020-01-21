(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn, Jakob von Raumer
*)

import .precategory types.sigma arity

open eq category prod equiv is_equiv sigma sigma.ops is_trunc

namespace iso
  structure split_mono [class] {ob : Type} [C : precategory ob] {a b : ob} (f : a ⟶ b).
    {retraction_of : b ⟶ a}
    (retraction_comp : retraction_of o f = id)
  structure split_epi [class] {ob : Type} [C : precategory ob] {a b : ob} (f : a ⟶ b).
    {section_of : b ⟶ a}
    (comp_section : f o section_of = id)
  structure is_iso [class] {ob : Type} [C : precategory ob] {a b : ob} (f : a ⟶ b).
    (inverse : b ⟶ a)
    (left_inverse  : inverse o f = id)
    (right_inverse : f o inverse = id)

  attribute is_iso.inverse [reducible]

  open split_mono split_epi is_iso
  abbreviation retraction_of . @split_mono.retraction_of
  abbreviation retraction_comp . @split_mono.retraction_comp
  abbreviation section_of . @split_epi.section_of
  abbreviation comp_section . @split_epi.comp_section
  abbreviation inverse . @is_iso.inverse
  abbreviation left_inverse . @is_iso.left_inverse
  abbreviation right_inverse . @is_iso.right_inverse
  postfix ^-1 . inverse
  --a second notation for the inverse, which is not overloaded
  postfix [parsing_only] `^-1ʰ`:std.prec.max_plus . inverse (* input using \-1h *)

  variables {ob : Type} [C : precategory ob]
  variables {a b c : ob} {g : b ⟶ c} {f : a ⟶ b} {h : b ⟶ a}
  include C

Definition split_mono_of_is_iso [instance] [priority 300]
    (f : a ⟶ b) [H : is_iso f] : split_mono f.
  split_mono.mk !left_inverse

Definition split_epi_of_is_iso [instance] [priority 300]
    (f : a ⟶ b) [H : is_iso f] : split_epi f.
  split_epi.mk !right_inverse

Definition is_iso_id [instance] [priority 500] (a : ob) : is_iso (ID a).
  is_iso.mk _ !id_id !id_id

Definition is_iso_inverse [instance] [priority 200] (f : a ⟶ b) {H : is_iso f}
    : is_iso f^-1.
  is_iso.mk _ !right_inverse !left_inverse

Definition left_inverse_eq_right_inverse {f : a ⟶ b} {g g' : hom b a}
      (Hl : g o f = id) (Hr : f o g' = id) : g = g'.
  by rewrite [-(id_right g), -Hr, assoc, Hl, id_left]

Definition retraction_eq [H : split_mono f] (H2 : f o h = id) : retraction_of f = h.
  left_inverse_eq_right_inverse !retraction_comp H2

Definition section_eq [H : split_epi f] (H2 : h o f = id) : section_of f = h.
  (left_inverse_eq_right_inverse H2 !comp_section)^-1

Definition inverse_eq_right [H : is_iso f] (H2 : f o h = id) : f^-1 = h.
  left_inverse_eq_right_inverse !left_inverse H2

Definition inverse_eq_left [H : is_iso f] (H2 : h o f = id) : f^-1 = h.
  (left_inverse_eq_right_inverse H2 !right_inverse)^-1

Definition retraction_eq_section (f : a ⟶ b) [Hl : split_mono f] [Hr : split_epi f] :
      retraction_of f = section_of f.
  retraction_eq !comp_section

Definition is_iso_of_split_epi_of_split_mono (f : a ⟶ b)
    [Hl : split_mono f] [Hr : split_epi f] : is_iso f.
  is_iso.mk _ ((retraction_eq_section f) # (retraction_comp f)) (comp_section f)

Definition inverse_unique (H H' : is_iso f) : @inverse _ _ _ _ f H = @inverse _ _ _ _ f H'.
  @inverse_eq_left _ _ _ _ _ _ H !left_inverse

Definition inverse_involutive (f : a ⟶ b) [H : is_iso f] [H : is_iso (f^-1)]
    : (f^-1)^-1 = f.
  inverse_eq_right !left_inverse

Definition inverse_eq_inverse {f g : a ⟶ b} [H : is_iso f] [H : is_iso g] (p : f = g)
    : f^-1 = g^-1.
  by cases p;apply inverse_unique

Definition retraction_id (a : ob) : retraction_of (ID a) = id.
  retraction_eq !id_id

Definition section_id (a : ob) : section_of (ID a) = id.
  section_eq !id_id

Definition id_inverse (a : ob) [H : is_iso (ID a)] : (ID a)^-1 = id.
  inverse_eq_left !id_id

Definition split_mono_comp [instance] [priority 150] (g : b ⟶ c) (f : a ⟶ b)
    [Hf : split_mono f] [Hg : split_mono g] : split_mono (g o f).
  split_mono.mk
    (show (retraction_of f o retraction_of g) o g o f = id,
     by rewrite [-assoc, assoc _ g f, retraction_comp, id_left, retraction_comp])

Definition split_epi_comp [instance] [priority 150] (g : b ⟶ c) (f : a ⟶ b)
    [Hf : split_epi f] [Hg : split_epi g] : split_epi (g o f).
  split_epi.mk
    (show (g o f) o section_of f o section_of g = id,
     by rewrite [-assoc, {f o _}assoc, comp_section, id_left, comp_section])

Definition is_iso_comp [instance] [priority 150] (g : b ⟶ c) (f : a ⟶ b)
    [Hf : is_iso f] [Hg : is_iso g] : is_iso (g o f).
  !is_iso_of_split_epi_of_split_mono

Definition is_prop_is_iso [instance] (f : hom a b) : is_prop (is_iso f).
Proof.
    apply is_prop.mk, intro H H',
    cases H with g li ri, cases H' with g' li' ri',
    fapply (apd0111 (@is_iso.mk ob C a b f)),
      apply left_inverse_eq_right_inverse,
        apply li,
        apply ri',
      apply is_prop.elimo,
      apply is_prop.elimo,
Defined.
Defined. iso open iso

(* isomorphic objects *)
structure iso {ob : Type} [C : precategory ob] (a b : ob).
  (to_hom : hom a b)
  (struct : is_iso to_hom)

  infix ` ≅ `:50 . iso
  notation c ` ≅[`:50 C:0 `] `:0 c':50 . @iso C _ c c'
  attribute iso.struct [instance] [priority 2000]

namespace iso
  variables {ob : Type} [C : precategory ob]
  variables {a b c : ob} {g : b ⟶ c} {f : a ⟶ b} {h : b ⟶ a}
  include C

  attribute to_hom [coercion]

  protectedDefinition MK (f : a ⟶ b) (g : b ⟶ a)
    (H1 : g o f = id) (H2 : f o g = id).
  @(mk f) (is_iso.mk _ H1 H2)

  variable {C}
Definition to_inv (f : a ≅ b) : b ⟶ a . (to_hom f)^-1
Definition to_left_inverse  (f : a ≅ b) : (to_hom f)^-1 o (to_hom f) = id.
  left_inverse  (to_hom f)
Definition to_right_inverse (f : a ≅ b) : (to_hom f) o (to_hom f)^-1 = id.
  right_inverse (to_hom f)

  variable [C]
  protectedDefinition refl (a : ob) : a ≅ a.
  mk (ID a) _

  protectedDefinition symm (a b : ob) (H : a ≅ b) : b ≅ a.
  mk (to_hom H)^-1 _

  protectedDefinition trans (a b c : ob) (H1 : a ≅ b) (H2 : b ≅ c) : a ≅ c.
  mk (to_hom H2 o to_hom H1) _

  infixl ` @i `:75 . iso.trans
  postfix `^-1ⁱ`:(max + 1) . iso.symm

Definition change_hom (H : a ≅ b) (f : a ⟶ b) (p : to_hom H = f) : a ≅ b.
  iso.MK f (to_inv H) (p # to_left_inverse H) (p # to_right_inverse H)

Definition change_inv (H : a ≅ b) (g : b ⟶ a) (p : to_inv H = g) : a ≅ b.
  iso.MK (to_hom H) g (p # to_left_inverse H) (p # to_right_inverse H)

Definition iso_mk_eq {f f' : a ⟶ b} [H : is_iso f] [H' : is_iso f'] (p : f = f')
      : iso.mk f _ = iso.mk f' _.
  apd011 iso.mk p !is_prop.elimo

  variable {C}
Definition iso_eq {f f' : a ≅ b} (p : to_hom f = to_hom f') : f = f'.
  by (cases f; cases f'; apply (iso_mk_eq p))

Definition iso_pathover {X : Type} {x₁ x₂ : X} {p : x₁ = x₂} {a : X -> ob} {b : X -> ob}
    {f₁ : a x₁ ≅ b x₁} {f₂ : a x₂ ≅ b x₂} (q : to_hom f₁ =[p] to_hom f₂) : f₁ =[p] f₂.
Proof.
    cases f₁, cases f₂, esimp at q, induction q, apply pathover_idp_of_eq,
    exact ap (iso.mk _) !is_prop.elim
Defined.
  variable [C]

  (* The structure for isomorphism can be characterized up to equivalence by a sigma type. *)
  protectedDefinition sigma_char (a b : ob) : (Σ (f : hom a b), is_iso f) <~> (a ≅ b).
Proof.
    fapply (equiv.mk),
      {intro S, apply iso.mk, apply (S.2)},
      {fapply adjointify,
        {intro p, cases p with f H, exact sigma.mk f H},
        {intro p, cases p, apply idp},
        {intro S, cases S, apply idp}},
Defined.

  (* The type of isomorphisms between two objects is a set *)
Definition is_set_iso [instance] : is_set (a ≅ b).
Proof.
    apply is_trunc_is_equiv_closed,
      apply equiv.to_is_equiv (!iso.sigma_char),
Defined.

Definition iso_of_eq (p : a = b) : a ≅ b.
  eq.rec_on p (iso.refl a)

Definition hom_of_eq (p : a = b) : a ⟶ b.
  iso.to_hom (iso_of_eq p)

Definition inv_of_eq (p : a = b) : b ⟶ a.
  iso.to_inv (iso_of_eq p)

Definition iso_of_eq_inv (p : a = b) : iso_of_eq p^-1 = iso.symm (iso_of_eq p).
  eq.rec_on p idp

Definition hom_of_eq_inv (p : a = b) : hom_of_eq p^-1 = inv_of_eq p.
  eq.rec_on p idp

Definition inv_of_eq_inv (p : a = b) : inv_of_eq p^-1 = hom_of_eq p.
  eq.rec_on p idp

Definition iso_of_eq_con (p : a = b) (q : b = c)
    : iso_of_eq (p @ q) = iso.trans (iso_of_eq p) (iso_of_eq q).
  eq.rec_on q (eq.rec_on p (iso_eq !id_id^-1))

Definition transport_iso_of_eq (p : a = b) :
    p # !iso.refl = iso_of_eq p.
  by cases p; reflexivity

Definition hom_pathover {X : Type} {x₁ x₂ : X} {p : x₁ = x₂} {a b : X -> ob}
    {f₁ : a x₁ ⟶ b x₁} {f₂ : a x₂ ⟶ b x₂} (q : hom_of_eq (ap b p) o f₁ = f₂ o hom_of_eq (ap a p)) :
    f₁ =[p] f₂.
Proof.
    induction p, apply pathover_idp_of_eq, exact !id_left^-1 @ q @ !id_right
Defined.

Definition hom_pathover_constant_left {X : Type} {x₁ x₂ : X} {p : x₁ = x₂} {a : ob} {b : X -> ob}
    {f₁ : a ⟶ b x₁} {f₂ : a ⟶ b x₂} (q : hom_of_eq (ap b p) o f₁ = f₂) : f₁ =[p] f₂.
  hom_pathover (q @ !id_right^-1 @ ap (fun x => _ o hom_of_eq x) (ap_pp _ _ _)stant^-1)

Definition hom_pathover_constant_right {X : Type} {x₁ x₂ : X} {p : x₁ = x₂} {a : X -> ob} {b : ob}
    {f₁ : a x₁ ⟶ b} {f₂ : a x₂ ⟶ b} (q : f₁ = f₂ o hom_of_eq (ap a p)) : f₁ =[p] f₂.
  hom_pathover (ap (fun x => hom_of_eq x o _) (ap_pp _ _ _)stant @ !id_left @ q)

Definition hom_pathover_id_left {p : a = b} {c : ob -> ob} {f₁ : a  ⟶ c a} {f₂ : b ⟶ c b}
    (q : hom_of_eq (ap c p) o f₁ = f₂ o hom_of_eq p) : f₁ =[p] f₂.
  hom_pathover (q @ ap (fun x => _ o hom_of_eq x) !ap_id^-1)

Definition hom_pathover_id_right {p : a = b} {c : ob -> ob} {f₁ : c a  ⟶ a} {f₂ : c b ⟶ b}
    (q : hom_of_eq p o f₁ = f₂ o hom_of_eq (ap c p)) : f₁ =[p] f₂.
  hom_pathover (ap (fun x => hom_of_eq x o _) !ap_id @ q)

Definition hom_pathover_id_left_id_right {p : a = b} {f₁ : a  ⟶ a} {f₂ : b ⟶ b}
    (q : hom_of_eq p o f₁ = f₂ o hom_of_eq p) : f₁ =[p] f₂.
  hom_pathover_id_left (ap (fun x => hom_of_eq x o _) !ap_id @ q)

Definition hom_pathover_id_left_constant_right {p : a = b} {f₁ : a  ⟶ c} {f₂ : b ⟶ c}
    (q : f₁ = f₂ o hom_of_eq p) : f₁ =[p] f₂.
  hom_pathover_constant_right (q @ ap (fun x => _ o hom_of_eq x) !ap_id^-1)

Definition hom_pathover_constant_left_id_right {p : a = b} {f₁ : c  ⟶ a} {f₂ : c ⟶ b}
    (q : hom_of_eq p o f₁ = f₂) : f₁ =[p] f₂.
  hom_pathover_constant_left (ap (fun x => hom_of_eq x o _) !ap_id @ q)

  section
    open funext
    variables {X : Type} {x y : X} {F G : X -> ob}
Definition transport_hom_of_eq (p : F = G) (f : hom (F x) (F y))
      : p # f = hom_of_eq (apd10 p y) o f o inv_of_eq (apd10 p x).
    by induction p; exact !id_leftright^-1

Definition transport_hom_of_eq_right (p : x = y) (f : hom c (F x))
      : p # f = hom_of_eq (ap F p) o f.
    by induction p; exact !id_left^-1

Definition transport_hom_of_eq_left (p : x = y) (f : hom (F x) c)
      : p # f = f o inv_of_eq (ap F p).
    by induction p; exact !id_right^-1

Definition transport_hom (p : F == G) (f : hom (F x) (F y))
      : eq_of_homotopy p # f = hom_of_eq (p y) o f o inv_of_eq (p x).
    calc
      eq_of_homotopy p # f =
        hom_of_eq (apd10 (eq_of_homotopy p) y) o f o inv_of_eq (apd10 (eq_of_homotopy p) x)
          : transport_hom_of_eq
        ... = hom_of_eq (p y) o f o inv_of_eq (p x) : {right_inv apd10 p}

Defined.

  structure mono [class] (f : a ⟶ b).
    (elim : ∀c (g h : hom c a), f o g = f o h -> g = h)
  structure epi  [class] (f : a ⟶ b).
    (elim : ∀c (g h : hom b c), g o f = h o f -> g = h)

Definition mono_of_split_mono [instance] (f : a ⟶ b) [H : split_mono f] : mono f.
  mono.mk
    (fun c g h H =>
      calc
        g = id o g                    : by rewrite id_left
      ... = (retraction_of f o f) o g : by rewrite retraction_comp
      ... = (retraction_of f o f) o h : by rewrite [-assoc, H, -assoc]
      ... = id o h                    : by rewrite retraction_comp
      ... = h                         : by rewrite id_left)

Definition epi_of_split_epi [instance] (f : a ⟶ b) [H : split_epi f] : epi f.
  epi.mk
    (fun c g h H =>
      calc
        g = g o id               : by rewrite id_right
      ... = g o f o section_of f : by rewrite -(comp_section f)
      ... = h o f o section_of f : by rewrite [assoc, H, -assoc]
      ... = h o id               : by rewrite comp_section
      ... = h                    : by rewrite id_right)

Definition mono_comp [instance] (g : b ⟶ c) (f : a ⟶ b) [Hf : mono f] [Hg : mono g]
    : mono (g o f).
  mono.mk
    (fun d h₁ h₂ H =>
    have H2 : g o (f o h₁) = g o (f o h₂),
    begin
      rewrite *assoc, exact H
    end,
    !mono.elim (!mono.elim H2))

Definition epi_comp  [instance] (g : b ⟶ c) (f : a ⟶ b) [Hf : epi f] [Hg : epi g]
    : epi  (g o f).
  epi.mk
    (fun d h₁ h₂ H =>
    have H2 : (h₁ o g) o f = (h₂ o g) o f,
    begin
      rewrite -*assoc, exact H
    end,
    !epi.elim (!epi.elim H2))

Defined. iso





namespace iso
  (*
  rewrite lemmas for inverses, modified from
  https://github.com/JasonGross/HoTT-categories/blob/master/theories/Categories/Category/Morphisms.v
  *)
  section
  variables {ob : Type} [C : precategory ob] include C
  variables {a b c d : ob}                         (f : b ⟶ a)
                           (r : c ⟶ d) (q : b ⟶ c) (p : a ⟶ b)
                           (g : d ⟶ c)
  variable [Hq : is_iso q] include Hq
Definition comp.right_inverse : q o q^-1 = id . !right_inverse
Definition comp.left_inverse : q^-1 o q = id . !left_inverse

Definition inverse_comp_cancel_left : q^-1 o (q o p) = p.
   by rewrite [assoc, left_inverse, id_left]
Definition comp_inverse_cancel_left : q o (q^-1 o g) = g.
   by rewrite [assoc, right_inverse, id_left]
Definition comp_inverse_cancel_right : (r o q) o q^-1 = r.
  by rewrite [-assoc, right_inverse, id_right]
Definition inverse_comp_cancel_right : (f o q^-1) o q = f.
  by rewrite [-assoc, left_inverse, id_right]

Definition comp_inverse [Hp : is_iso p] [Hpq : is_iso (q o p)] : (q o p)^-1ʰ = p^-1ʰ o q^-1ʰ.
  inverse_eq_left
    (show (p^-1ʰ o q^-1ʰ) o q o p = id, from
     by rewrite [-assoc, inverse_comp_cancel_left, left_inverse])

Definition inverse_comp_inverse_left [H' : is_iso g] : (q^-1 o g)^-1 = g^-1 o q.
  inverse_involutive q # comp_inverse q^-1 g

Definition inverse_comp_inverse_right [H' : is_iso f] : (q o f^-1)^-1 = f o q^-1.
  inverse_involutive f # comp_inverse q f^-1

Definition inverse_comp_inverse_inverse [H' : is_iso r] : (q^-1 o r^-1)^-1 = r o q.
  inverse_involutive r # inverse_comp_inverse_left q r^-1
Defined.

  section
  variables {ob : Type} {C : precategory ob} include C
  variables {d           c           b           a : ob}
             {r' : c ⟶ d} {i : b ⟶ c} {f : b ⟶ a}
              {r : c ⟶ d} {q : b ⟶ c} {p : a ⟶ b}
              {g : d ⟶ c} {h : c ⟶ b} {p' : a ⟶ b}
                   {x : b ⟶ d} {z : a ⟶ c}
                   {y : d ⟶ b} {w : c ⟶ a}
  variable [Hq : is_iso q] include Hq

Definition comp_eq_of_eq_inverse_comp (H : y = q^-1 o g) : q o y = g.
  H^-1 # comp_inverse_cancel_left q g
Definition comp_eq_of_eq_comp_inverse (H : w = f o q^-1) : w o q = f.
  H^-1 # inverse_comp_cancel_right f q
Definition eq_comp_of_inverse_comp_eq (H : q^-1 o g = y) : g = q o y.
  (comp_eq_of_eq_inverse_comp H^-1)^-1
Definition eq_comp_of_comp_inverse_eq (H : f o q^-1 = w) : f = w o q.
  (comp_eq_of_eq_comp_inverse H^-1)^-1
  variable {Hq}
Definition inverse_comp_eq_of_eq_comp (H : z = q o p) : q^-1 o z = p.
  H^-1 # inverse_comp_cancel_left q p
Definition comp_inverse_eq_of_eq_comp (H : x = r o q) : x o q^-1 = r.
  H^-1 # comp_inverse_cancel_right r q
Definition eq_inverse_comp_of_comp_eq (H : q o p = z) : p = q^-1 o z.
  (inverse_comp_eq_of_eq_comp H^-1)^-1
Definition eq_comp_inverse_of_comp_eq (H : r o q = x) : r = x o q^-1.
  (comp_inverse_eq_of_eq_comp H^-1)^-1

Definition eq_inverse_of_comp_eq_id' (H : h o q = id) : h = q^-1 . (inverse_eq_left H)^-1
Definition eq_inverse_of_comp_eq_id (H : q o h = id) : h = q^-1 . (inverse_eq_right H)^-1
Definition inverse_eq_of_id_eq_comp (H : id = h o q) : q^-1 = h.
  (eq_inverse_of_comp_eq_id' H^-1)^-1
Definition inverse_eq_of_id_eq_comp' (H : id = q o h) : q^-1 = h.
  (eq_inverse_of_comp_eq_id H^-1)^-1
  variable [Hq]
Definition eq_of_comp_inverse_eq_id (H : i o q^-1 = id) : i = q.
  eq_inverse_of_comp_eq_id' H @ inverse_involutive q
Definition eq_of_inverse_comp_eq_id (H : q^-1 o i = id) : i = q.
  eq_inverse_of_comp_eq_id H @ inverse_involutive q
Definition eq_of_id_eq_comp_inverse (H : id = i o q^-1) : q = i . (eq_of_comp_inverse_eq_id H^-1)^-1
Definition eq_of_id_eq_inverse_comp (H : id = q^-1 o i) : q = i . (eq_of_inverse_comp_eq_id H^-1)^-1

Definition inverse_comp_id_comp : q^-1 o id o q = id.
  ap (fun x => _ o x) !id_left @ !comp.left_inverse
Definition comp_id_comp_inverse : q o id o q^-1 = id.
  ap (fun x => _ o x) !id_left @ !comp.right_inverse

  variables (q)
Definition comp.cancel_left  (H : q o p = q o p') : p = p'.
  by rewrite [-inverse_comp_cancel_left q p, H, inverse_comp_cancel_left q]
Definition comp.cancel_right (H : r o q = r' o q) : r = r'.
  by rewrite [-comp_inverse_cancel_right r q, H, comp_inverse_cancel_right _ q]
Defined.
Defined. iso

namespace iso

  (* precomposition and postcomposition by an iso is an equivalence *)

Definition is_equiv_postcompose {ob : Type} [precategory ob] {a b c : ob}
    (g : b ⟶ c) [is_iso g] : is_equiv (fun (f : a ⟶ b) => g o f).
Proof.
    fapply adjointify,
    { exact fun f' => g^-1 o f'},
    { intro f', apply comp_inverse_cancel_left},
    { intro f, apply inverse_comp_cancel_left}
Defined.

Definition equiv_postcompose {ob : Type} [precategory ob] {a b c : ob}
    (g : b ⟶ c) [is_iso g] : (a ⟶ b) <~> (a ⟶ c).
  equiv.mk (fun (f : a ⟶ b) => g o f) (is_equiv_postcompose g)

Definition is_equiv_precompose {ob : Type} [precategory ob] {a b c : ob}
    (f : a ⟶ b) [is_iso f] : is_equiv (fun (g : b ⟶ c) => g o f).
Proof.
    fapply adjointify,
    { exact fun g' => g' o f^-1},
    { intro g', apply comp_inverse_cancel_right},
    { intro g, apply inverse_comp_cancel_right}
Defined.

Definition equiv_precompose {ob : Type} [precategory ob] {a b c : ob}
    (f : a ⟶ b) [is_iso f] : (b ⟶ c) <~> (a ⟶ c).
  equiv.mk (fun (g : b ⟶ c) => g o f) (is_equiv_precompose f)

Defined. iso
