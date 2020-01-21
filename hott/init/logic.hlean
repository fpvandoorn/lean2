(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Floris van Doorn
*)

prelude
import init.reserved_notation
open unit

Definition id [unfold_full] {A : Type} (a : A) : A.
a

(* not *)

Definition not (a : Type) . a -> empty
prefix ¬ . not

Definition absurd {a b : Type} (H₁ : a) (H₂ : ¬a) : b.
empty.rec (fun e => b) (H₂ H₁)

Definition mt {a b : Type} (H₁ : a -> b) (H₂ : ¬b) : ¬a.
assume Ha : a, absurd (H₁ Ha) H₂

Definition not_empty : ¬empty.
assume H : empty, H

Definition non_contradictory (a : Type) : Type . ¬¬a

Definition non_contradictory_intro {a : Type} (Ha : a) : ¬¬a.
assume Hna : ¬a, absurd Ha Hna

Definition not.intro {a : Type} (H : a -> empty) : ¬a . H

(* empty *)

Definition empty.elim {c : Type} (H : empty) : c.
empty.rec _ H

(* eq *)

infix = . eq
Definition rfl {A : Type} {a : A} . eq.refl a

(*
  These notions are here only to make porting from the standard library easier.
  They are defined again in init/path.hlean, and thoseDefinitions will be used
  throughout the HoTT-library. That's why the notation for eq below is only local.
*)
namespace eq
  variables {A : Type} {a b c : A}

Definition subst {P : A -> Type} (H₁ : a = b) (H₂ : P a) : P b.
  eq.rec H₂ H₁

Definition trans (H₁ : a = b) (H₂ : b = c) : a = c.
  subst H₂ H₁

Definition symm (H : a = b) : b = a.
  subst H (refl a)

Definition mp {a b : Type} : (a = b) -> a -> b.
  eq.rec_on

Definition mpr {a b : Type} : (a = b) -> b -> a.
  assume H₁ H₂, eq.rec_on (eq.symm H₁) H₂

  namespace ops end ops (* this is just to ensure that this namespace exists. There is nothing in it *)
Defined. eq

local postfix ^-1 . eq.symm --input with \sy or \-1 or \inv
local infixl @ . eq.trans
local infixr # . eq.subst

(* AuxiliaryDefinition used by automation. It has the same type of eq.rec in the standard library *)
Definition eq.nrec.{l₁ l₂} {A : Type.{l₂}} {a : A} {C : A -> Type.{l₁}} (H₁ : C a) (b : A) (H₂ : a = b) : C b.
eq.rec H₁ H₂

Definition congr {A B : Type} {f₁ f₂ : A -> B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂.
eq.subst H₁ (eq.subst H₂ rfl)

Definition congr_fun {A : Type} {B : A -> Type} {f g : forall , B x} (H : f = g) (a : A) : f a = g a.
eq.subst H (eq.refl (f a))

Definition congr_arg {A B : Type} (a a' : A) (f : A -> B) (Ha : a = a') : f a = f a'.
eq.subst Ha rfl

Definition congr_arg2 {A B C : Type} (a a' : A) (b b' : B) (f : A -> B -> C) (Ha : a = a') (Hb : b = b') : f a b = f a' b'.
eq.subst Ha (eq.subst Hb rfl)

section
  variables {A : Type} {a b c: A}
  open eq.ops

Definition trans_rel_left (R : A -> A -> Type) (H₁ : R a b) (H₂ : b = c) : R a c.
  H₂ # H₁

Definition trans_rel_right (R : A -> A -> Type) (H₁ : a = b) (H₂ : R b c) : R a c.
  H₁^-1 # H₂
Defined.






namespace lift
Definition down_up.{l₁ l₂} {A : Type.{l₁}} (a : A) : down (up.{l₁ l₂} a) = a.
  rfl

Definition up_down.{l₁ l₂} {A : Type.{l₁}} (a : lift.{l₁ l₂} A) : up (down a) = a.
  lift.rec_on a (fun d => rfl)
Defined. lift

(* ne *)

Definition ne {A : Type} (a b : A) . ¬(a = b)
notation a ≠ b . ne a b

namespace ne
  open eq.ops
  variable {A : Type}
  variables {a b : A}

Definition intro (H : a = b -> empty) : a ≠ b . H

Definition elim (H : a ≠ b) : a = b -> empty . H

Definition irrefl (H : a ≠ a) : empty . H rfl

Definition symm (H : a ≠ b) : b ≠ a.
  assume (H₁ : b = a), H (H₁^-1)
Defined. ne

Definition empty_of_ne {A : Type} {a : A} : a ≠ a -> empty . ne.irrefl

section
  open eq.ops
  variables {p : Type₀}

Definition ne_empty_of_self : p -> p ≠ empty.
  assume (Hp : p) (Heq : p = empty), Heq # Hp

Definition ne_unit_of_not : ¬p -> p ≠ unit.
  assume (Hnp : ¬p) (Heq : p = unit), (Heq # Hnp) star

Definition unit_ne_empty : ¬unit = empty.
  ne_empty_of_self star
Defined.

(* prod *)

abbreviation pair . @prod.mk
infixr \* . prod

variables {a b c d : Type}




protectedDefinition prod.elim (H₁ : a \* b) (H₂ : a -> b -> c) : c.
prod.rec H₂ H₁

Definition prod.swap : a \* b -> b \* a.
prod.rec (fun Ha Hb => prod.mk Hb Ha)

(* sum *)

infixr ⊎ . sum



protectedDefinition sum.elim (H₁ : a ⊎ b) (H₂ : a -> c) (H₃ : b -> c) : c.
sum.rec H₂ H₃ H₁

Definition non_contradictory_em (a : Type) : ¬¬(a ⊎ ¬a).
assume not_em : ¬(a ⊎ ¬a),
  have neg_a : ¬a, from
    assume pos_a : a, absurd (sum.inl pos_a) not_em,
  absurd (sum.inr neg_a) not_em

Definition sum.swap : a ⊎ b -> b ⊎ a . sum.rec sum.inr sum.inl


(* iff *)

Definition iff (a b : Type) . (a -> b) \* (b -> a)

notation a <-> b . iff a b
notation a ↔ b . iff a b

Definition iff.intro : (a -> b) -> (b -> a) -> (a ↔ b) . prod.mk



Definition iff.elim : ((a -> b) -> (b -> a) -> c) -> (a ↔ b) -> c . prod.rec



Definition iff.elim_left : (a ↔ b) -> a -> b . prod.pr1

Definition iff.mp . @iff.elim_left

Definition iff.elim_right : (a ↔ b) -> b -> a . prod.pr2

Definition iff.mpr . @iff.elim_right

Definition iff.refl [refl] (a : Type) : a ↔ a.
iff.intro (assume H, H) (assume H, H)

Definition iff.rfl {a : Type} : a ↔ a.
iff.refl a

Definition iff.trans [trans] (H₁ : a ↔ b) (H₂ : b ↔ c) : a ↔ c.
iff.intro
  (assume Ha, iff.mp H₂ (iff.mp H₁ Ha))
  (assume Hc, iff.mpr H₁ (iff.mpr H₂ Hc))

Definition iff.symm [symm] (H : a ↔ b) : b ↔ a.
iff.intro (iff.elim_right H) (iff.elim_left H)

Definition iff.comm : (a ↔ b) ↔ (b ↔ a).
iff.intro iff.symm iff.symm

Definition iff.of_eq {a b : Type} (H : a = b) : a ↔ b.
eq.rec_on H iff.rfl

Definition not_iff_not_of_iff (H₁ : a ↔ b) : ¬a ↔ ¬b.
iff.intro
 (assume (Hna : ¬ a) (Hb : b), Hna (iff.elim_right H₁ Hb))
 (assume (Hnb : ¬ b) (Ha : a), Hnb (iff.elim_left H₁ Ha))

Definition of_iff_unit (H : a ↔ unit) : a.
iff.mp (iff.symm H) star

Definition not_of_iff_empty : (a ↔ empty) -> ¬a . iff.mp

Definition iff_unit_intro (H : a) : a ↔ unit.
iff.intro
  (fun Hl => star)
  (fun Hr => H)

Definition iff_empty_intro (H : ¬a) : a ↔ empty.
iff.intro H (empty.rec _)

Definition not_non_contradictory_iff_absurd (a : Type) : ¬¬¬a ↔ ¬a.
iff.intro
  (fun (Hl : ¬¬¬a) (Ha : a) => Hl (non_contradictory_intro Ha))
  absurd

Definition imp_congr [congr] (H1 : a ↔ c) (H2 : b ↔ d) : (a -> b) ↔ (c -> d).
iff.intro
  (fun Hab Hc => iff.mp H2 (Hab (iff.mpr H1 Hc)))
  (fun Hcd Ha => iff.mpr H2 (Hcd (iff.mp H1 Ha)))

Definition not_not_intro (Ha : a) : ¬¬a.
assume Hna : ¬a, Hna Ha

Definition not_of_not_not_not (H : ¬¬¬a) : ¬a.
fun Ha => absurd (not_not_intro Ha) H

Definition not_unit [simp] : (¬ unit) ↔ empty.
iff_empty_intro (not_not_intro star)

Definition not_empty_iff [simp] : (¬ empty) ↔ unit.
iff_unit_intro not_empty

Definition not_congr (H : a ↔ b) : ¬a ↔ ¬b.
iff.intro (fun H₁ H₂ => H₁ (iff.mpr H H₂)) (fun H₁ H₂ => H₁ (iff.mp H H₂))

Definition ne_self_iff_empty [simp] {A : Type} (a : A) : (not (a = a)) ↔ empty.
iff.intro empty_of_ne empty.elim

Definition eq_self_iff_unit [simp] {A : Type} (a : A) : (a = a) ↔ unit.
iff_unit_intro rfl

Definition iff_not_self [simp] (a : Type) : (a ↔ ¬a) ↔ empty.
iff_empty_intro (fun H =>
   have H' : ¬a, from (fun Ha => (iff.mp H Ha) Ha),
   H' (iff.mpr H H'))

Definition not_iff_self [simp] (a : Type) : (¬a ↔ a) ↔ empty.
iff_empty_intro (fun H =>
   have H' : ¬a, from (fun Ha => (iff.mpr H Ha) Ha),
   H' (iff.mp H H'))

Definition unit_iff_empty [simp] : (unit ↔ empty) ↔ empty.
iff_empty_intro (fun H => iff.mp H star)

Definition empty_iff_unit [simp] : (empty ↔ unit) ↔ empty.
iff_empty_intro (fun H => iff.mpr H star)

Definition empty_of_unit_iff_empty : (unit ↔ empty) -> empty.
assume H, iff.mp H star

(* prod simp rules *)
Definition prod.imp (H₂ : a -> c) (H₃ : b -> d) : a \* b -> c \* d.
prod.rec (fun Ha Hb => prod.mk (H₂ Ha) (H₃ Hb))

Definition prod_congr [congr] (H1 : a ↔ c) (H2 : b ↔ d) : (a \* b) ↔ (c \* d).
iff.intro (prod.imp (iff.mp H1) (iff.mp H2)) (prod.imp (iff.mpr H1) (iff.mpr H2))

Definition prod.comm [simp] : a \* b ↔ b \* a.
iff.intro prod.swap prod.swap

Definition prod.assoc [simp] : (a \* b) \* c ↔ a \* (b \* c).
iff.intro
  (prod.rec (fun H' Hc => prod.rec (fun Ha Hb => prod.mk Ha (prod.mk Hb Hc)) H'))
  (prod.rec (fun Ha => prod.rec (fun Hb Hc => prod.mk (prod.mk Ha Hb) Hc)))

Definition prod.pr1_comm [simp] : a \* (b \* c) ↔ b \* (a \* c).
iff.trans (iff.symm !prod.assoc) (iff.trans (prod_congr !prod.comm !iff.refl) !prod.assoc)

Definition prod_iff_left {a b : Type} (Hb : b) : (a \* b) ↔ a.
iff.intro prod.pr1 (fun Ha => prod.mk Ha Hb)

Definition prod_iff_right {a b : Type} (Ha : a) : (a \* b) ↔ b.
iff.intro prod.pr2 (prod.mk Ha)

Definition prod_unit [simp] (a : Type) : a \* unit ↔ a.
prod_iff_left star

Definition unit_prod [simp] (a : Type) : unit \* a ↔ a.
prod_iff_right star

Definition prod_empty [simp] (a : Type) : a \* empty ↔ empty.
iff_empty_intro prod.pr2

Definition empty_prod [simp] (a : Type) : empty \* a ↔ empty.
iff_empty_intro prod.pr1

Definition not_prod_self [simp] (a : Type) : (¬a \* a) ↔ empty.
iff_empty_intro (fun H => prod.elim H (fun H₁ H₂ => absurd H₂ H₁))

Definition prod_not_self [simp] (a : Type) : (a \* ¬a) ↔ empty.
iff_empty_intro (fun H => prod.elim H (fun H₁ H₂ => absurd H₁ H₂))

Definition prod_self [simp] (a : Type) : a \* a ↔ a.
iff.intro prod.pr1 (assume H, prod.mk H H)

(* sum simp rules *)

Definition sum.imp (H₂ : a -> c) (H₃ : b -> d) : a ⊎ b -> c ⊎ d.
sum.rec (fun H => sum.inl (H₂ H)) (fun H => sum.inr (H₃ H))

Definition sum.imp_left (H : a -> b) : a ⊎ c -> b ⊎ c.
sum.imp H id

Definition sum.imp_right (H : a -> b) : c ⊎ a -> c ⊎ b.
sum.imp id H

Definition sum_congr [congr] (H1 : a ↔ c) (H2 : b ↔ d) : (a ⊎ b) ↔ (c ⊎ d).
iff.intro (sum.imp (iff.mp H1) (iff.mp H2)) (sum.imp (iff.mpr H1) (iff.mpr H2))

Definition sum.comm [simp] : a ⊎ b ↔ b ⊎ a . iff.intro sum.swap sum.swap

Definition sum.assoc [simp] : (a ⊎ b) ⊎ c ↔ a ⊎ (b ⊎ c).
iff.intro
  (sum.rec (sum.imp_right sum.inl) (fun H => sum.inr (sum.inr H)))
  (sum.rec (fun H => sum.inl (sum.inl H)) (sum.imp_left sum.inr))

Definition sum.left_comm [simp] : a ⊎ (b ⊎ c) ↔ b ⊎ (a ⊎ c).
iff.trans (iff.symm !sum.assoc) (iff.trans (sum_congr !sum.comm !iff.refl) !sum.assoc)

Definition sum_unit [simp] (a : Type) : a ⊎ unit ↔ unit.
iff_unit_intro (sum.inr star)

Definition unit_sum [simp] (a : Type) : unit ⊎ a ↔ unit.
iff_unit_intro (sum.inl star)

Definition sum_empty [simp] (a : Type) : a ⊎ empty ↔ a.
iff.intro (sum.rec id empty.elim) sum.inl

Definition empty_sum [simp] (a : Type) : empty ⊎ a ↔ a.
iff.trans sum.comm !sum_empty

Definition sum_self [simp] (a : Type) : a ⊎ a ↔ a.
iff.intro (sum.rec id id) sum.inl

(* sum resolution rulse *)

Definition sum.resolve_left {a b : Type} (H : a ⊎ b) (na : ¬ a) : b.
  sum.elim H (fun Ha => absurd Ha na) id

Definition sum.neg_resolve_left {a b : Type} (H : ¬ a ⊎ b) (Ha : a) : b.
  sum.elim H (fun na => absurd Ha na) id

Definition sum.resolve_right {a b : Type} (H : a ⊎ b) (nb : ¬ b) : a.
  sum.elim H id (fun Hb => absurd Hb nb)

Definition sum.neg_resolve_right {a b : Type} (H : a ⊎ ¬ b) (Hb : b) : a.
  sum.elim H id (fun nb => absurd Hb nb)

(* iff simp rules *)

Definition iff_unit [simp] (a : Type) : (a ↔ unit) ↔ a.
iff.intro (assume H, iff.mpr H star) iff_unit_intro

Definition unit_iff [simp] (a : Type) : (unit ↔ a) ↔ a.
iff.trans iff.comm !iff_unit

Definition iff_empty [simp] (a : Type) : (a ↔ empty) ↔ ¬ a.
iff.intro prod.pr1 iff_empty_intro

Definition empty_iff [simp] (a : Type) : (empty ↔ a) ↔ ¬ a.
iff.trans iff.comm !iff_empty

Definition iff_self [simp] (a : Type) : (a ↔ a) ↔ unit.
iff_unit_intro iff.rfl

Definition iff_congr [congr] (H1 : a ↔ c) (H2 : b ↔ d) : (a ↔ b) ↔ (c ↔ d).
prod_congr (imp_congr H1 H2) (imp_congr H2 H1)

(* decidable *)

inductive decidable [class] (p : Type) : Type.
| inl :  p -> decidable p
| inr : ¬p -> decidable p

Definition decidable_unit [instance] : decidable unit.
decidable.inl star

Definition decidable_empty [instance] : decidable empty.
decidable.inr not_empty

(* We use "dependent" if-then-else to be able to communicate the if-then-else condition *)
(* to the branches *)
Definition dite (c : Type) [H : decidable c] {A : Type} : (c -> A) -> (¬ c -> A) -> A.
decidable.rec_on H

(* if-then-else *)

Definition ite (c : Type) [H : decidable c] {A : Type} (t e : A) : A.
decidable.rec_on H (fun Hc => t) (fun Hnc => e)

namespace decidable
  variables {p q : Type}

Definition by_cases {q : Type} [C : decidable p] : (p -> q) -> (¬p -> q) -> q . !dite

Definition em (p : Type) [H : decidable p] : p ⊎ ¬p . by_cases sum.inl sum.inr

Definition by_contradiction [Hp : decidable p] (H : ¬p -> empty) : p.
  if H1 : p then H1 else empty.rec _ (H H1)
Defined. decidable

section
  variables {p q : Type}
  open decidable
Definition  decidable_of_decidable_of_iff (Hp : decidable p) (H : p ↔ q) : decidable q.
  if Hp : p then inl (iff.mp H Hp)
  else inr (iff.mp (not_iff_not_of_iff H) Hp)

Definition decidable_of_decidable_of_eq {p q : Type} (Hp : decidable p) (H : p = q)
    : decidable q.
  decidable_of_decidable_of_iff Hp (iff.of_eq H)

  protectedDefinition sum.by_cases [Hp : decidable p] [Hq : decidable q] {A : Type}
                                   (h : p ⊎ q) (h₁ : p -> A) (h₂ : q -> A) : A.
  if hp : p then h₁ hp else
    if hq : q then h₂ hq else
      empty.rec _ (sum.elim h hp hq)
Defined.

section
  variables {p q : Type}
  open decidable (rec_on inl inr)

Definition decidable_prod [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p \* q).
  if hp : p then
    if hq : q then inl (prod.mk hp hq)
    else inr (assume H : p \* q, hq (prod.pr2 H))
  else inr (assume H : p \* q, hp (prod.pr1 H))

Definition decidable_sum [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ⊎ q).
  if hp : p then inl (sum.inl hp) else
    if hq : q then inl (sum.inr hq) else
      inr (sum.rec hp hq)

Definition decidable_not [instance] [Hp : decidable p] : decidable (¬p).
  if hp : p then inr (absurd hp) else inl hp

Definition decidable_implies [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p -> q).
  if hp : p then
    if hq : q then inl (assume H, hq)
    else inr (assume H : p -> q, absurd (H hp) hq)
  else inl (assume Hp, absurd Hp hp)

Definition decidable_iff [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ↔ q).
  decidable_prod

Defined.

Definition decidable_pred {A : Type} (R : A   ->   Type) . forall (a   : A), decidable (R a)
Definition decidable_rel  {A : Type} (R : A -> A -> Type) . forall (a b : A), decidable (R a b)
Definition decidable_eq   (A : Type) . decidable_rel (@eq A)
Definition decidable_ne [instance] {A : Type} [H : decidable_eq A] (a b : A) : decidable (a ≠ b).
decidable_implies

namespace bool
Definition ff_ne_tt : ff = tt -> empty
  | [none]
Defined. bool

open bool
Definition is_dec_eq {A : Type} (p : A -> A -> bool) : Type   . forall (x y : A), p x y = tt -> x = y
Definition is_dec_refl {A : Type} (p : A -> A -> bool) : Type . forall x, p x x = tt

open decidable
protectedDefinition bool.has_decidable_eq [instance] : forall a b : bool, decidable (a = b)
| ff ff . inl rfl
| ff tt . inr ff_ne_tt
| tt ff . inr (ne.symm ff_ne_tt)
| tt tt . inl rfl

Definition decidable_eq_of_bool_pred {A : Type} {p : A -> A -> bool} (H₁ : is_dec_eq p) (H₂ : is_dec_refl p) : decidable_eq A.
take x y : A, if Hp : p x y = tt then inl (H₁ Hp)
 else inr (assume Hxy : x = y, (eq.subst Hxy Hp) (H₂ y))

(* inhabited *)

inductive inhabited [class] (A : Type) : Type.
mk : A -> inhabited A

protectedDefinition inhabited.value {A : Type} : inhabited A -> A.
inhabited.rec (fun a => a)

protectedDefinition inhabited.destruct {A : Type} {B : Type} (H1 : inhabited A) (H2 : A -> B) : B.
inhabited.rec H2 H1

Definition default (A : Type) [H : inhabited A] : A.
inhabited.value H

Definition arbitrary [irreducible] (A : Type) [H : inhabited A] : A.
inhabited.value H

Definition Type.is_inhabited [instance] : inhabited Type.
inhabited.mk (lift unit)

Definition inhabited_fun [instance] (A : Type) {B : Type} [H : inhabited B] : inhabited (A -> B).
inhabited.rec_on H (fun b => inhabited.mk (fun a => b))

Definition inhabited_Pi [instance] (A : Type) {B : A -> Type} [H : forall x, inhabited (B x)] :
  inhabited (forall x, B x).
inhabited.mk (fun a => !default)

protectedDefinition bool.is_inhabited [instance] : inhabited bool.
inhabited.mk ff

protectedDefinition pos_num.is_inhabited [instance] : inhabited pos_num.
inhabited.mk pos_num.one

protectedDefinition num.is_inhabited [instance] : inhabited num.
inhabited.mk num.zero

inductive nonempty [class] (A : Type) : Type.
intro : A -> nonempty A

protectedDefinition nonempty.elim {A : Type} {B : Type} (H1 : nonempty A) (H2 : A -> B) : B.
nonempty.rec H2 H1

Definition nonempty_of_inhabited [instance] {A : Type} [H : inhabited A] : nonempty A.
nonempty.intro !default

Definition nonempty_of_exists {A : Type} {P : A -> Type} : (sigma P) -> nonempty A.
sigma.rec (fun w H => nonempty.intro w)

(* subsingleton *)

inductive subsingleton [class] (A : Type) : Type.
intro : (forall a b : A, a = b) -> subsingleton A

protectedDefinition subsingleton.elim {A : Type} [H : subsingleton A] : forall (a b : A), a = b.
subsingleton.rec (fun p => p) H

protectedDefinition rec_subsingleton {p : Type} [H : decidable p]
    {H1 : p -> Type} {H2 : ¬p -> Type}
    [H3 : forall (h : p), subsingleton (H1 h)] [H4 : forall (h : ¬p), subsingleton (H2 h)]
  : subsingleton (decidable.rec_on H H1 H2).
decidable.rec_on H (fun h => H3 h) (fun h => H4 h) --this can be proven using dependent version of "by_cases"

Definition if_pos {c : Type} [H : decidable c] (Hc : c) {A : Type} {t e : A} : (ite c t e) = t.
decidable.rec
  (fun Hc : c =>    eq.refl (@ite c (decidable.inl Hc) A t e))
  (fun Hnc : ¬c =>  absurd Hc Hnc)
  H

Definition if_neg {c : Type} [H : decidable c] (Hnc : ¬c) {A : Type} {t e : A} : (ite c t e) = e.
decidable.rec
  (fun Hc : c =>    absurd Hc Hnc)
  (fun Hnc : ¬c =>  eq.refl (@ite c (decidable.inr Hnc) A t e))
  H

Definition if_t_t [simp] (c : Type) [H : decidable c] {A : Type} (t : A) : (ite c t t) = t.
decidable.rec
  (fun Hc  : c =>  eq.refl (@ite c (decidable.inl Hc)  A t t))
  (fun Hnc : ¬c => eq.refl (@ite c (decidable.inr Hnc) A t t))
  H

Definition implies_of_if_pos {c t e : Type} [H : decidable c] (h : ite c t e) : c -> t.
assume Hc, eq.rec_on (if_pos Hc) h

Definition implies_of_if_neg {c t e : Type} [H : decidable c] (h : ite c t e) : ¬c -> e.
assume Hnc, eq.rec_on (if_neg Hnc) h

Definition if_ctx_congr {A : Type} {b c : Type} [dec_b : decidable b] [dec_c : decidable c]
                     {x y u v : A}
                     (h_c : b ↔ c) (h_t : c -> x = u) (h_e : ¬c -> y = v) :
        ite b x y = ite c u v.
decidable.rec_on dec_b
  (fun hp : b => calc
    ite b x y = x           : if_pos hp
         ...  = u           : h_t (iff.mp h_c hp)
         ...  = ite c u v : if_pos (iff.mp h_c hp))
  (fun hn : ¬b => calc
    ite b x y = y         : if_neg hn
         ...  = v         : h_e (iff.mp (not_iff_not_of_iff h_c) hn)
         ...  = ite c u v : if_neg (iff.mp (not_iff_not_of_iff h_c) hn))

Definition if_congr [congr] {A : Type} {b c : Type} [dec_b : decidable b] [dec_c : decidable c]
                 {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = ite c u v.
@if_ctx_congr A b c dec_b dec_c x y u v h_c (fun h => h_t) (fun h => h_e)

Definition if_ctx_simp_congr {A : Type} {b c : Type} [dec_b : decidable b] {x y u v : A}
                        (h_c : b ↔ c) (h_t : c -> x = u) (h_e : ¬c -> y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v).
@if_ctx_congr A b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x y u v h_c h_t h_e

Definition if_simp_congr [congr] {A : Type} {b c : Type} [dec_b : decidable b] {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v).
@if_ctx_simp_congr A b c dec_b x y u v h_c (fun h => h_t) (fun h => h_e)

Definition if_unit [simp] {A : Type} (t e : A) : (if unit then t else e) = t.
if_pos star

Definition if_empty [simp] {A : Type} (t e : A) : (if empty then t else e) = e.
if_neg not_empty

Definition if_ctx_congr_prop {b c x y u v : Type} [dec_b : decidable b] [dec_c : decidable c]
                      (h_c : b ↔ c) (h_t : c -> (x ↔ u)) (h_e : ¬c -> (y ↔ v)) :
        ite b x y ↔ ite c u v.
decidable.rec_on dec_b
  (fun hp : b => calc
    ite b x y ↔ x         : iff.of_eq (if_pos hp)
         ...  ↔ u         : h_t (iff.mp h_c hp)
         ...  ↔ ite c u v : iff.of_eq (if_pos (iff.mp h_c hp)))
  (fun hn : ¬b => calc
    ite b x y ↔ y         : iff.of_eq (if_neg hn)
         ...  ↔ v         : h_e (iff.mp (not_iff_not_of_iff h_c) hn)
         ...  ↔ ite c u v : iff.of_eq (if_neg (iff.mp (not_iff_not_of_iff h_c) hn)))

Definition if_congr_prop [congr] {b c x y u v : Type} [dec_b : decidable b] [dec_c : decidable c]
                      (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ ite c u v.
if_ctx_congr_prop h_c (fun h => h_t) (fun h => h_e)

Definition if_ctx_simp_congr_prop {b c x y u v : Type} [dec_b : decidable b]
                               (h_c : b ↔ c) (h_t : c -> (x ↔ u)) (h_e : ¬c -> (y ↔ v)) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) Type u v).
@if_ctx_congr_prop b c x y u v dec_b (decidable_of_decidable_of_iff dec_b h_c) h_c h_t h_e

Definition if_simp_congr_prop [congr] {b c x y u v : Type} [dec_b : decidable b]
                           (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) Type u v).
@if_ctx_simp_congr_prop b c x y u v dec_b h_c (fun h => h_t) (fun h => h_e)

(* Remark: dite and ite are "Definitionally equal" when we ignore the proofs. *)
Definition dite_ite_eq (c : Type) [H : decidable c] {A : Type} (t : A) (e : A) : dite c (fun h => t) (fun h => e) = ite c t e.
rfl

Definition is_unit (c : Type) [H : decidable c] : Type₀.
if c then unit else empty

Definition is_empty (c : Type) [H : decidable c] : Type₀.
if c then empty else unit

Definition of_is_unit {c : Type} [H₁ : decidable c] (H₂ : is_unit c) : c.
decidable.rec_on H₁ (fun Hc => Hc) (fun Hnc => empty.rec _ (if_neg Hnc # H₂))

notation `dec_star` . of_is_unit star

Definition not_of_not_is_unit {c : Type} [H₁ : decidable c] (H₂ : ¬ is_unit c) : ¬ c.
if Hc : c then absurd star (if_pos Hc # H₂) else Hc

Definition not_of_is_empty {c : Type} [H₁ : decidable c] (H₂ : is_empty c) : ¬ c.
if Hc : c then empty.rec _ (if_pos Hc # H₂) else Hc

Definition of_not_is_empty {c : Type} [H₁ : decidable c] (H₂ : ¬ is_empty c) : c.
if Hc : c then Hc else absurd star (if_neg Hc # H₂)

(* The following symbols should not be considered in the pattern inference procedure used by *)
(* heuristic instantiation. *)


(* namespace used to collect congruence rules for "contextual simplification" *)
namespace contextual
  attribute if_ctx_simp_congr      [congr]
  attribute if_ctx_simp_congr_prop [congr]
Defined. contextual
