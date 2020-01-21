(*
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer
*)

import ..iso types.pi

open function category eq prod prod.ops equiv is_equiv sigma sigma.ops is_trunc funext iso pi

structure functor (C D : Precategory) : Type.
  (to_fun_ob : C -> D)
  (to_fun_hom : forall , hom a b -> hom (to_fun_ob a) (to_fun_ob b))
  (respect_id : forall (a : C), to_fun_hom (ID a) = ID (to_fun_ob a))
  (respect_comp : forall {a b c : C} (g : hom b c) (f : hom a b),
    to_fun_hom (g o f) = to_fun_hom g o to_fun_hom f)

namespace functor

  infixl ` ⇒ `:55 . functor
  variables {A B C D E : Precategory}

  attribute to_fun_ob [coercion]
  attribute to_fun_hom [coercion]

  (* The following lemmas will later be used to prove that the type of *)
  (* precategories forms a precategory itself *)
  protectedDefinition compose (G : functor D E) (F : functor C D)
    : functor C E.
  functor.mk
    (fun x => G (F x))
    (fun a b f => G (F f))
    (fun a => abstract calc
      G (F (ID a)) = G (ID (F a)) : by rewrite respect_id
               ... = ID (G (F a)) : by rewrite respect_id end)
    (fun a b c g f => abstract calc
      G (F (g o f)) = G (F g o F f)     : by rewrite respect_comp
                ... = G (F g) o G (F f) : by rewrite respect_comp end)

  infixr ` of `:75 . functor.compose

  protectedDefinition id {C : Precategory} : functor C C.
  mk (fun a => a) (fun a b f => f) (fun a => idp) (fun a b c f g => idp)

  protectedDefinition ID (C : Precategory) : functor C C . @functor.id C
  notation 1 . functor.id

Definition constant_functor (C : Precategory) {D : Precategory} (d : D) : C ⇒ D.
  functor.mk (fun c => d)
             (fun c c' f => id)
             (fun c => idp)
             (fun a b c g f => !id_id^-1)

  (* introduction rule for equalities between functors *)
Definition functor_mk_eq' {F₁ F₂ : C -> D} {H₁ : forall , hom a b -> hom (F₁ a) (F₁ b)}
    {H₂ : forall (a b : C), hom a b -> hom (F₂ a) (F₂ b)} (id₁ id₂ comp₁ comp₂)
    (pF : F₁ = F₂) (pH : pF # H₁ = H₂)
      : functor.mk F₁ H₁ id₁ comp₁ = functor.mk F₂ H₂ id₂ comp₂.
  apdt01111 functor.mk pF pH !is_prop.elim !is_prop.elim

Definition functor_eq' {F₁ F₂ : C ⇒ D} : forall ,
    (transport (fun x => forall a b f, hom (x a) (x b)) p @(to_fun_hom F₁) = @(to_fun_hom F₂)) -> F₁ = F₂.
  by induction F₁; induction F₂; apply functor_mk_eq'

Definition functor_mk_eq {F₁ F₂ : C -> D} {H₁ : forall , hom a b -> hom (F₁ a) (F₁ b)}
    {H₂ : forall (a b : C), hom a b -> hom (F₂ a) (F₂ b)} (id₁ id₂ comp₁ comp₂) (pF : F₁ == F₂)
    (pH : forall (a b : C) (f : hom a b), hom_of_eq (pF b) o H₁ a b f o inv_of_eq (pF a) = H₂ a b f)
      : functor.mk F₁ H₁ id₁ comp₁ = functor.mk F₂ H₂ id₂ comp₂.
Proof.
    fapply functor_mk_eq' =>
    { exact eq_of_homotopy pF},
    { refine eq_of_homotopy (fun c => eq_of_homotopy (fun c' => eq_of_homotopy (fun f => _))), intros,
      rewrite [+pi_transport_constant,-pH,-transport_hom]}
Defined.

Definition functor_eq {F₁ F₂ : C ⇒ D} : forall ,
    (forall (a b : C) (f : hom a b), hom_of_eq (p b) o F₁ f o inv_of_eq (p a) = F₂ f) -> F₁ = F₂.
  by induction F₁; induction F₂; apply functor_mk_eq

Definition functor_mk_eq_constant {F : C -> D} {H₁ : forall , hom a b -> hom (F a) (F b)}
    {H₂ : forall (a b : C), hom a b -> hom (F a) (F b)} (id₁ id₂ comp₁ comp₂)
    (pH : forall (a b : C) (f : hom a b), H₁ a b f = H₂ a b f)
      : functor.mk F H₁ id₁ comp₁ = functor.mk F H₂ id₂ comp₂.
  functor_eq (fun c => idp) (fun a b f => !id_leftright @ !pH)

Definition preserve_is_iso (F : C ⇒ D) {a b : C} (f : hom a b) [H : is_iso f]
    : is_iso (F f).
Proof.
    fapply @is_iso.mk, apply (F (f^-1)),
    repeat (apply concat ; symmetry ;  apply (respect_comp F) ;
      apply concat ; apply (ap (fun x => to_fun_hom F x)) ;
      (apply iso.left_inverse | apply iso.right_inverse);
      apply (respect_id F) ),
Defined.

Definition respect_inv (F : C ⇒ D) {a b : C} (f : hom a b) [H : is_iso f] [H' : is_iso (F f)] :
    F (f^-1) = (F f)^-1.
Proof.
    fapply @left_inverse_eq_right_inverse, apply (F f),
      transitivity to_fun_hom F (f^-1 o f) =>
        {symmetry, apply (respect_comp F)},
        {transitivity to_fun_hom F category.id =>
          {congruence, apply iso.left_inverse},
          {apply respect_id}},
      apply iso.right_inverse
Defined.

  attribute preserve_is_iso [instance] [priority 100]

Definition to_fun_iso (F : C ⇒ D) {a b : C} (f : a ≅ b) : F a ≅ F b.
  iso.mk (F f) _

Definition respect_inv' (F : C ⇒ D) {a b : C} (f : hom a b) {H : is_iso f} : F (f^-1) = (F f)^-1.
  respect_inv F f

Definition respect_refl (F : C ⇒ D) (a : C) : to_fun_iso F (iso.refl a) = iso.refl (F a).
  iso_eq !respect_id

Definition respect_symm (F : C ⇒ D) {a b : C} (f : a ≅ b)
    : to_fun_iso F f^-1ⁱ = (to_fun_iso F f)^-1ⁱ.
  iso_eq !respect_inv

Definition respect_trans (F : C ⇒ D) {a b c : C} (f : a ≅ b) (g : b ≅ c)
    : to_fun_iso F (f @i g) = to_fun_iso F f @i to_fun_iso F g.
  iso_eq !respect_comp

Definition respect_iso_of_eq (F : C ⇒ D) {a b : C} (p : a = b) :
    to_fun_iso F (iso_of_eq p) = iso_of_eq (ap F p).
  by induction p; apply respect_refl

Definition respect_hom_of_eq (F : C ⇒ D) {a b : C} (p : a = b) :
    F (hom_of_eq p) = hom_of_eq (ap F p).
  by induction p; apply respect_id

Definition respect_inv_of_eq (F : C ⇒ D) {a b : C} (p : a = b) :
    F (inv_of_eq p) = inv_of_eq (ap F p).
  by induction p; apply respect_id

  protectedDefinition assoc (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B) :
      H of (G of F) = (H of G) of F.
  !functor_mk_eq_constant (fun a b f => idp)

  protectedDefinition id_left  (F : C ⇒ D) : 1 of F = F.
  functor.rec_on F (fun F1 F2 F3 F4 => !functor_mk_eq_constant (fun a b f => idp))

  protectedDefinition id_right (F : C ⇒ D) : F of 1 = F.
  functor.rec_on F (fun F1 F2 F3 F4 => !functor_mk_eq_constant (fun a b f => idp))

  protectedDefinition comp_id_eq_id_comp (F : C ⇒ D) : F of 1 = 1 of F.
  !functor.id_right @ !functor.id_left^-1

Definition functor_of_eq {C D : Precategory} (p : C = D :> Precategory) : C ⇒ D.
  functor.mk (transport carrier p)
             (fun a b f => by induction p; exact f)
             (by intro c; induction p; reflexivity)
             (by intros; induction p; reflexivity)

  protectedDefinition sigma_char :
    (Σ (to_fun_ob : C -> D)
    (to_fun_hom : forall ,
    (forall (a : C), to_fun_hom (ID a) = ID (to_fun_ob a)) \*
    (forall {a b c : C} (g : hom b c) (f : hom a b),
      to_fun_hom (g o f) = to_fun_hom g o to_fun_hom f)) <~> (functor C D).
Proof.
    fapply equiv.MK,
      {intro S, induction S with d1 S2, induction S2 with d2 P1, induction P1 with P11 P12,
       exact functor.mk d1 d2 P11 @P12} =>
      {intro F, induction F with d1 d2 d3 d4, exact ⟨d1, @d2, (d3, @d4)⟩},
      {intro F, induction F, reflexivity},
      {intro S, induction S with d1 S2, induction S2 with d2 P1, induction P1, reflexivity},
Defined.

Definition change_fun (F : C ⇒ D) (Fob : C -> D)
    (Fhom : forall (c c' : C) (f : c ⟶ c'), Fob c ⟶ Fob c') (p : F = Fob) (q : F =[p] Fhom) : C ⇒ D.
  functor.mk
    Fob
    Fhom
    proof abstract fun a => transporto (fun Fo (Fh : forall , _), Fh (ID a) = ID (Fo a))
      q (respect_id F a) end qed
    proof abstract fun a b c g f => transporto (fun Fo (Fh : forall , _), Fh (g o f) = Fh g o Fh f)
      q (respect_comp F g f) end qed

  section
    local attribute precategory.is_set_hom [instance] [priority 1001]
    local attribute trunctype.struct [instance] [priority 1] (* remove after #842 is closed *)
    protectedDefinition is_set_functor [instance]
      [HD : is_set D] : is_set (functor C D).
    by apply is_trunc_equiv_closed; apply functor.sigma_char
Defined.

  (* higher equalities in the functor type *)
Definition functor_mk_eq'_idp (F : C -> D) (H : forall , hom a b -> hom (F a) (F b))
    (id comp) : functor_mk_eq' id id comp comp (idpath F) (idpath H) = idp.
Proof.
    fapply apd011 (apdt01111 functor.mk idp idp) =>
    apply is_prop.elim,
    apply is_prop.elimo
Defined.

Definition functor_eq'_idp (F : C ⇒ D) : functor_eq' idp idp = (idpath F).
  by (cases F; apply functor_mk_eq'_idp)

Definition functor_eq_eta' {F₁ F₂ : C ⇒ D} (p : F₁ = F₂)
      : functor_eq' (ap to_fun_ob p) (!tr_compose^-1 @ apdt to_fun_hom p) = p.
Proof.
    cases p, cases F₁,
    refine _ @ !functor_eq'_idp =>
    esimp
Defined.

Definition functor_eq2' {F₁ F₂ : C ⇒ D} {p₁ p₂ : to_fun_ob F₁ = to_fun_ob F₂} (q₁ q₂)
    (r : p₁ = p₂) : functor_eq' p₁ q₁ = functor_eq' p₂ q₂.
  by cases r; apply (ap (functor_eq' p₂)); apply is_prop.elim

Definition functor_eq2 {F₁ F₂ : C ⇒ D} (p q : F₁ = F₂) (r : ap010 to_fun_ob p == ap010 to_fun_ob q)
    : p = q.
Proof.
    cases F₁ with ob₁ hom₁ id₁ comp₁,
    cases F₂ with ob₂ hom₂ id₂ comp₂,
    rewrite [-functor_eq_eta' p => -functor_eq_eta' q] =>
    apply functor_eq2' =>
    apply ap_eq_ap_of_homotopy,
    exact r,
Defined.

Definition ap010_apd01111_functor {F₁ F₂ : C -> D} {H₁ : forall , hom a b -> hom (F₁ a) (F₁ b)}
    {H₂ : forall (a b : C), hom a b -> hom (F₂ a) (F₂ b)} {id₁ id₂ comp₁ comp₂}
    (pF : F₁ = F₂) (pH : pF # H₁ = H₂) (pid : cast (apdt011 _ pF pH) id₁ = id₂)
    (pcomp : cast (apdt0111 _ pF pH pid) comp₁ = comp₂) (c : C)
      : ap010 to_fun_ob (apdt01111 functor.mk pF pH pid pcomp) c = ap10 pF c.
  by induction pF; induction pH; induction pid; induction pcomp; reflexivity

Definition ap010_functor_eq {F₁ F₂ : C ⇒ D} (p : to_fun_ob F₁ == to_fun_ob F₂)
    (q : (fun (a b : C) (f : hom a b) => hom_of_eq (p b) o F₁ f o inv_of_eq (p a)) ~3 @(to_fun_hom F₂))
    (c : C) : ap010 to_fun_ob (functor_eq p q) c = p c.
Proof.
    cases F₁ with F₁o F₁h F₁id F₁comp, cases F₂ with F₂o F₂h F₂id F₂comp,
    esimp [functor_eq =>functor_mk_eq =>functor_mk_eq'] =>
    rewrite [ap010_apd01111_functor =>↑ap10,{apd10 (eq_of_homotopy p)}right_inv apd10]
Defined.

Definition ap010_functor_mk_eq_constant {F : C -> D} {H₁ : forall , hom a b -> hom (F a) (F b)}
    {H₂ : forall (a b : C), hom a b -> hom (F a) (F b)} {id₁ id₂ comp₁ comp₂}
    (pH : forall (a b : C) (f : hom a b), H₁ a b f = H₂ a b f) (c : C) :
  ap010 to_fun_ob (functor_mk_eq_constant id₁ id₂ comp₁ comp₂ pH) c = idp.
  !ap010_functor_eq

Definition ap010_assoc (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B) (a : A) :
    ap010 to_fun_ob (functor.assoc H G F) a = idp.
  by apply ap010_functor_mk_eq_constant

Definition compose_pentagon (K : D ⇒ E) (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B) :
    (calc K of H of G of F = (K of H) of G of F : functor.assoc
      ... = ((K of H) of G) of F : functor.assoc)
    =
    (calc K of H of G of F = K of (H of G) of F : ap (fun x => K of x) !functor.assoc
      ... = (K of H of G) of F : functor.assoc
      ... = ((K of H) of G) of F : ap (fun x => x of F) !functor.assoc).
Proof.
  have lem1  : forall {F₁ F₂ : A ⇒ D} (p : F₁ = F₂) (a : A),
    ap010 to_fun_ob (ap (fun x => K of x) p) a = ap (to_fun_ob K) (ap010 to_fun_ob p a) =>
      by intros; cases p; esimp,
  have lem2 : forall {F₁ F₂ : B ⇒ E} (p : F₁ = F₂) (a : A),
    ap010 to_fun_ob (ap (fun x => x of F) p) a = ap010 to_fun_ob p (F a) =>
      by intros; cases p; esimp,
  apply functor_eq2 =>
  intro a, esimp,
  rewrite [+ap010_con,lem1,lem2,
            ap010_assoc K H (G of F) a,
            ap010_assoc (K of H) G F a,
            ap010_assoc H G F a,
            ap010_assoc K H G (F a),
            ap010_assoc K (H of G) F a],
Defined.

Definition hom_pathover_functor {c₁ c₂ : C} {p : c₁ = c₂} (F G : C ⇒ D)
    {f₁ : F c₁ ⟶ G c₁} {f₂ : F c₂ ⟶ G c₂}
    (q : to_fun_hom G (hom_of_eq p) o f₁ = f₂ o to_fun_hom F (hom_of_eq p)) : f₁ =[p] f₂.
  hom_pathover (hom_whisker_right _ (respect_hom_of_eq G _)^-1 @ q @
                hom_whisker_left _ (respect_hom_of_eq F _))

Definition hom_pathover_constant_left_functor_right {c₁ c₂ : C} {p : c₁ = c₂} {d : D} (F : C ⇒ D)
    {f₁ : d ⟶ F c₁} {f₂ : d ⟶ F c₂} (q : to_fun_hom F (hom_of_eq p) o f₁ = f₂) : f₁ =[p] f₂.
  hom_pathover_constant_left (hom_whisker_right _ (respect_hom_of_eq F _)^-1 @ q)

Definition hom_pathover_functor_left_constant_right {c₁ c₂ : C} {p : c₁ = c₂} {d : D} (F : C ⇒ D)
    {f₁ : F c₁ ⟶ d} {f₂ : F c₂ ⟶ d} (q : f₁ = f₂ o to_fun_hom F (hom_of_eq p)) : f₁ =[p] f₂.
  hom_pathover_constant_right (q @ hom_whisker_left _ (respect_hom_of_eq F _))

Definition hom_pathover_id_left_functor_right {c₁ c₂ : C} {p : c₁ = c₂} (F : C ⇒ C)
    {f₁ : c₁ ⟶ F c₁} {f₂ : c₂ ⟶ F c₂} (q : to_fun_hom F (hom_of_eq p) o f₁ = f₂ o hom_of_eq p) :
    f₁ =[p] f₂.
  hom_pathover_id_left (hom_whisker_right _ (respect_hom_of_eq F _)^-1 @ q)

Definition hom_pathover_functor_left_id_right {c₁ c₂ : C} {p : c₁ = c₂} (F : C ⇒ C)
    {f₁ : F c₁ ⟶ c₁} {f₂ : F c₂ ⟶ c₂} (q : hom_of_eq p o f₁ = f₂ o to_fun_hom F (hom_of_eq p)) :
    f₁ =[p] f₂.
  hom_pathover_id_right (q @ hom_whisker_left _ (respect_hom_of_eq F _))


Defined. functor
