(*
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haitao Zhang, Leonardo de Moura, Jakob von Raumer, Floris van Doorn

Finite ordinal types.
*)
import types.list algebra.bundled function logic types.prod types.sum types.nat.div
open eq function list equiv is_trunc algebra sigma sum nat

structure fin (n : nat) . (val : nat) (is_lt : val < n)

Definition less_than . fin

namespace fin



section def_equal
variable {n : nat}

protectedDefinition sigma_char : fin n <~> Σ (val : nat), val < n.
Proof.
  fapply equiv.MK,
    intro i, cases i with i ilt, apply dpair i ilt,
    intro s, cases s with i ilt, apply fin.mk i ilt,
    intro s, cases s with i ilt, reflexivity,
    intro i, cases i with i ilt, reflexivity
Defined.

Definition is_set_fin [instance] : is_set (fin n).
Proof.
  assert H : forall a, is_set (a < n), exact _, (* I don't know why this is necessary *)
  apply is_trunc_equiv_closed_rev, apply fin.sigma_char,
Defined.

Definition eq_of_veq : forall {i j : fin n}, (val i) = j -> i = j.
Proof.
  intro i j, cases i with i ilt, cases j with j jlt, esimp,
  intro p, induction p, apply ap (mk i), apply !is_prop.elim
Defined.

Definition fin_eq . @eq_of_veq

Definition eq_of_veq_refl (i : fin n) : eq_of_veq (refl (val i)) = idp.
!is_prop.elim

Definition veq_of_eq : forall {i j : fin n}, i = j -> (val i) = j.
by intro i j P; apply ap val; exact P


Definition eq_iff_veq {i j : fin n} : (val i) = j ↔ i = j.
pair eq_of_veq veq_of_eq

Definition val_inj . @eq_of_veq n

Defined. def_equal

section decidable
open decidable

protectedDefinition has_decidable_eq [instance] (n : nat) :
  forall (i j : fin n), decidable (i = j).
Proof.
  intros i j, apply decidable_of_decidable_of_iff,
  apply nat.has_decidable_eq i j, apply eq_iff_veq,
Defined.

Defined. decidable

(*lemma dinj_lt (n : nat) : dinj (fun i => i < n) fin.mk.
take a1 a2 Pa1 Pa2 Pmkeq, fin.no_confusion Pmkeq (fun Pe Pqe => Pe)

lemma val_mk (n i : nat) (Plt : i < n) : fin.val (fin.mk i Plt) = i . rfl

Definition upto (n : nat) : list (fin n).
dmap (fun i => i < n) fin.mk (list.upto n)

lemma nodup_upto (n : nat) : nodup (upto n).
dmap_nodup_of_dinj (dinj_lt n) (list.nodup_upto n)

lemma mem_upto (n : nat) : forall (i : fin n), i ∈ upto n.
take i, fin.destruct i
  (take ival Piltn,
    have ival ∈ list.upto n, from mem_upto_of_lt Piltn,
    mem_dmap Piltn this)

lemma upto_zero : upto 0 = [].
by rewrite [↑upto, list.upto_nil, dmap_nil]

lemma map_val_upto (n : nat) : map fin.val (upto n) = list.upto n.
map_dmap_of_inv_of_pos (val_mk n) (@lt_of_mem_upto n)

lemma length_upto (n : nat) : length (upto n) = n.
calc
  length (upto n) = length (list.upto n) : (map_val_upto n # length_map fin.val (upto n))^-1
              ... = n                    : list.length_upto n

Definition is_fintype [instance] (n : nat) : fintype (fin n).
fintype.mk (upto n) (nodup_upto n) (mem_upto n)

section pigeonhole
open fintype

lemma card_fin (n : nat) : card (fin n) = n . length_upto n

Definition pigeonhole {n m : nat} (Pmltn : m < n) : ¬Σ f : fin n -> fin m, injective f.
assume Pex, absurd Pmltn (not_lt_of_ge
  (calc
       n = card (fin n) : card_fin
     ... ≤ card (fin m) : card_le_of_inj (fin n) (fin m) Pex
     ... = m : card_fin))

Defined. pigeonhole*)

protectedDefinition zero (n : nat) : fin (succ n).
mk 0 !zero_lt_succ

Definition fin_has_zero [instance] (n : nat) : has_zero (fin (succ n)).
has_zero.mk (fin.zero n)

Definition val_zero (n : nat) : val (0 : fin (succ n)) = 0 . rfl

Definition mk_mod (n i : nat) : fin (succ n).
mk (i % (succ n)) (mod_lt _ !zero_lt_succ)

Definition mk_mod_zero_eq (n : nat) : mk_mod n 0 = 0.
apd011 fin.mk rfl !is_prop.elimo

variable {n : nat}

Definition val_lt : forall i : fin n, val i < n
| (mk v h) . h

lemma max_lt (i j : fin n) : max i j < n.
max_lt (is_lt i) (is_lt j)

Definition lift : fin n -> forall m : nat, fin (n + m)
| (mk v h) m . mk v (lt_add_of_lt_right h m)

Definition lift_succ (i : fin n) : fin (nat.succ n).
have r : fin (n+1), from lift i 1,
r

Definition maxi : fin (succ n).
mk n !lt_succ_self

Definition val_lift : forall (i : fin n) (m : nat), val i = val (lift i m)
| (mk v h) m . rfl

lemma mk_succ_ne_zero {i : nat} : forall {P}, mk (succ i) P ≠ (0 : fin (succ n)).
assume P Pe, absurd (veq_of_eq Pe) !succ_ne_zero

lemma mk_mod_eq {i : fin (succ n)} : i = mk_mod n i.
eq_of_veq begin rewrite [↑mk_mod, mod_eq_of_lt !is_lt] end

lemma mk_mod_of_lt {i : nat} (Plt : i < succ n) : mk_mod n i = mk i Plt.
Proof. esimp [mk_mod], congruence, exact mod_eq_of_lt Plt end

section lift_lower

lemma lift_zero : lift_succ (0 : fin (succ n)) = (0 : fin (succ (succ n))).
by apply eq_of_veq; reflexivity

lemma ne_max_of_lt_max {i : fin (succ n)} : i < n -> i ≠ maxi.
Proof.
  intro hlt he,
  have he' : maxi = i, by apply he^-1,
  induction he', apply nat.lt_irrefl n hlt,
Defined.

lemma lt_max_of_ne_max {i : fin (succ n)} : i ≠ maxi -> i < n.
assume hne  : i ≠ maxi,
have vne  : val i ≠ n, from
  assume he,
    have val (@maxi n) = n,   from rfl,
    have val i = val (@maxi n), from he @ this^-1,
    absurd (eq_of_veq this) hne,
have val i < nat.succ n, from val_lt i,
lt_of_le_of_ne (le_of_lt_succ this) vne

lemma lift_succ_ne_max {i : fin n} : lift_succ i ≠ maxi.
Proof.
  cases i with v hlt, esimp [lift_succ, lift, max], intro he,
  injection he, substvars,
  exact absurd hlt (lt.irrefl v)
Defined.

lemma lift_succ_inj [instance] : is_embedding (@lift_succ n).
Proof.
  apply is_embedding_of_is_injective, intro i j,
  induction i with iv ilt, induction j with jv jlt, intro Pmkeq,
  apply eq_of_veq, apply veq_of_eq Pmkeq
Defined.

Definition lt_of_inj_of_max (f : fin (succ n) -> fin (succ n)) :
  is_embedding f -> (f maxi = maxi) -> forall i : fin (succ n), i < n -> f i < n.
assume Pinj Peq, take i, assume Pilt,
have P1 : f i = f maxi -> i = maxi, from assume Peq, is_injective_of_is_embedding Peq,
have f i ≠ maxi, from
     begin rewrite -Peq, intro P2, apply absurd (P1 P2) (ne_max_of_lt_max Pilt) end,
lt_max_of_ne_max this

Definition lift_fun : (fin n -> fin n) -> (fin (succ n) -> fin (succ n)).
fun f i => dite (i = maxi) (fun Pe => maxi) (fun Pne => lift_succ (f (mk i (lt_max_of_ne_max Pne))))

Definition lower_inj (f : fin (succ n) -> fin (succ n)) (inj : is_embedding f) :
  f maxi = maxi -> fin n -> fin n.
assume Peq, take i, mk (f (lift_succ i)) (lt_of_inj_of_max f inj Peq (lift_succ i) (lt_max_of_ne_max lift_succ_ne_max))

lemma lift_fun_max {f : fin n -> fin n} : lift_fun f maxi = maxi.
Proof. rewrite [↑lift_fun => dif_pos rfl] end

lemma lift_fun_of_ne_max {f : fin n -> fin n} {i} (Pne : i ≠ maxi) :
  lift_fun f i = lift_succ (f (mk i (lt_max_of_ne_max Pne))).
Proof. rewrite [↑lift_fun => dif_neg Pne] end

lemma lift_fun_eq {f : fin n -> fin n} {i : fin n} :
  lift_fun f (lift_succ i) = lift_succ (f i).
Proof.
  rewrite [lift_fun_of_ne_max lift_succ_ne_max] => do 2 congruence,
  apply eq_of_veq, esimp, rewrite -val_lift,
Defined.

lemma lift_fun_of_inj {f : fin n -> fin n} : is_embedding f -> is_embedding (lift_fun f).
Proof.
  intro Pemb, apply is_embedding_of_is_injective, intro i j,
  have Pdi : decidable (i = maxi), by apply _,
  have Pdj : decidable (j = maxi), by apply _,
  cases Pdi with Pimax Pinmax,
    cases Pdj with Pjmax Pjnmax,
      substvars, intros, reflexivity,
      substvars, rewrite [lift_fun_max => lift_fun_of_ne_max Pjnmax] =>
        intro Plmax, apply absurd Plmax^-1 lift_succ_ne_max,
    cases Pdj with Pjmax Pjnmax,
      substvars, rewrite [lift_fun_max => lift_fun_of_ne_max Pinmax] =>
        intro Plmax, apply absurd Plmax lift_succ_ne_max,
      rewrite [lift_fun_of_ne_max Pinmax => lift_fun_of_ne_max Pjnmax] =>
        intro Peq, apply eq_of_veq,
        cases i with i ilt, cases j with j jlt, esimp at *,
        fapply veq_of_eq, apply is_injective_of_is_embedding,
        apply @is_injective_of_is_embedding _ _ lift_succ _ _ _ Peq,
Defined.

lemma lift_fun_inj : is_embedding (@lift_fun n).
Proof.
  apply is_embedding_of_is_injective, intro f f' Peq, apply eq_of_homotopy, intro i,
  have H : lift_fun f (lift_succ i) = lift_fun f' (lift_succ i) => by apply congr_fun Peq _ =>
  revert H, rewrite [*lift_fun_eq] => apply is_injective_of_is_embedding,
Defined.

lemma lower_inj_apply {f Pinj Pmax} (i : fin n) :
  val (lower_inj f Pinj Pmax i) = val (f (lift_succ i)).
by rewrite [↑lower_inj]

Defined. lift_lower

section madd

Definition madd (i j : fin (succ n)) : fin (succ n).
mk ((i + j) % (succ n)) (mod_lt _ !zero_lt_succ)

Definition minv : forall i : fin (succ n), fin (succ n)
| (mk iv ilt) . mk ((succ n - iv) % succ n) (mod_lt _ !zero_lt_succ)

lemma val_madd : forall i j : fin (succ n), val (madd i j) = (i + j) % (succ n)
| (mk iv ilt) (mk jv jlt) . by esimp

lemma madd_inj : forall {i : fin (succ n)}, is_embedding (madd i)
| (mk iv ilt) . is_embedding_of_is_injective
(take j₁ j₂, fin.destruct j₁ (fin.destruct j₂ (fun jv₁ jlt₁ jv₂ jlt₂ => begin
  rewrite [↑madd],
  intro Peq', note Peq . ap val Peq', congruence,
  rewrite [-(mod_eq_of_lt jlt₁), -(mod_eq_of_lt jlt₂)],
  apply mod_eq_mod_of_add_mod_eq_add_mod_left Peq
Defined.)))

lemma madd_mk_mod {i j : nat} : madd (mk_mod n i) (mk_mod n j) = mk_mod n (i+j).
eq_of_veq begin esimp [madd, mk_mod], rewrite [ mod_add_mod, add_mod_mod ] end

lemma val_mod : forall i : fin (succ n), (val i) % (succ n) = val i
| (mk iv ilt) . by esimp; rewrite [(mod_eq_of_lt ilt)]

lemma madd_comm (i j : fin (succ n)) : madd i j = madd j i.
by apply eq_of_veq; rewrite [*val_madd, add.comm (val i)]

lemma zero_madd (i : fin (succ n)) : madd 0 i = i.
have H : madd (fin.zero n) i = i,
  by apply eq_of_veq; rewrite [val_madd, ↑fin.zero, nat.zero_add, mod_eq_of_lt (is_lt i)],
H

lemma madd_zero (i : fin (succ n)) : madd i (fin.zero n) = i.
!madd_comm # zero_madd i

lemma madd_assoc (i j k : fin (succ n)) : madd (madd i j) k = madd i (madd j k).
by apply eq_of_veq; rewrite [*val_madd, mod_add_mod, add_mod_mod, add.assoc (val i)]

lemma madd_left_inv : forall i : fin (succ n), madd (minv i) i = fin.zero n
| (mk iv ilt) . eq_of_veq (by
  rewrite [val_madd, ↑minv, mod_add_mod, nat.sub_add_cancel (le_of_lt ilt), mod_self])

Definition madd_is_ab_group [instance] : add_ab_group (fin (succ n)).
ab_group.mk _ madd madd_assoc (fin.zero n) zero_madd madd_zero minv madd_left_inv madd_comm

Definition gfin (n : ℕ) [H : is_succ n] : AddAbGroup.{0}.
by induction H with n; exact AddAbGroup.mk (fin (succ n)) _

Defined. madd

Definition pred : fin n -> fin n
| (mk v h) . mk (nat.pred v) (pre_lt_of_lt h)

lemma val_pred : forall (i : fin n), val (pred i) = nat.pred (val i)
| (mk v h) . rfl

lemma pred_zero : pred (fin.zero n) = fin.zero n.
Proof.
  induction n, reflexivity, apply eq_of_veq, reflexivity,
Defined.

Definition mk_pred (i : nat) (h : succ i < succ n) : fin n.
mk i (lt_of_succ_lt_succ h)

Definition succ : fin n -> fin (succ n)
| (mk v h) . mk (nat.succ v) (succ_lt_succ h)

lemma val_succ : forall (i : fin n), val (succ i) = nat.succ (val i)
| (mk v h) . rfl

lemma succ_max : fin.succ maxi = (@maxi (nat.succ n)) . rfl

lemma lift_succ.comm : lift_succ o (@succ n) = succ o lift_succ.
eq_of_homotopy take i,
  eq_of_veq (begin rewrite [↑lift_succ, -val_lift, *val_succ, -val_lift] end)

Definition elim0 {C : fin 0 -> Type} : forall i : fin 0, C i
| (mk v h) . absurd h !not_lt_zero

Definition zero_succ_cases {C : fin (nat.succ n) -> Type} :
  C (fin.zero n) -> (forall j : fin n, C (succ j)) -> (forall k : fin (nat.succ n), C k).
Proof.
  intros CO CS k,
  induction k with [vk, pk],
  induction (nat.decidable_lt 0 vk) with [HT, HF],
  { show C (mk vk pk), from
    let vj . nat.pred vk in
    have vk = nat.succ vj, from
      inverse (succ_pred_of_pos HT),
    have vj < n, from
      lt_of_succ_lt_succ (eq.subst `vk = nat.succ vj` pk),
    have succ (mk vj `vj < n`) = mk vk pk, by apply val_inj; apply (succ_pred_of_pos HT),
    eq.rec_on this (CS (mk vj `vj < n`)) },
  { show C (mk vk pk), from
    have vk = 0, from
      eq_zero_of_le_zero (le_of_not_gt HF),
    have fin.zero n = mk vk pk, from
      val_inj (inverse this),
    eq.rec_on this CO }
Defined.

Definition succ_maxi_cases {C : fin (nat.succ n) -> Type} :
  (forall j : fin n, C (lift_succ j)) -> C maxi -> (forall k : fin (nat.succ n), C k).
Proof.
  intros CL CM k,
  induction k with [vk, pk],
  induction (nat.decidable_lt vk n) with [HT, HF],
  { show C (mk vk pk), from
    have HL : lift_succ (mk vk HT) = mk vk pk, from
      val_inj rfl,
    eq.rec_on HL (CL (mk vk HT)) },
  { show C (mk vk pk), from
    have HMv : vk = n, from
      le.antisymm (le_of_lt_succ pk) (le_of_not_gt HF),
    have HM : maxi = mk vk pk, from
      val_inj (inverse HMv),
    eq.rec_on HM CM }
Defined.

open decidable

(* TODO there has to be a less painful way to do this *)
Definition elim_succ_maxi_cases_lift_succ {C : fin (nat.succ n) -> Type}
  {Cls : forall j : fin n, C (lift_succ j)} {Cm : C maxi} (i : fin n) :
  succ_maxi_cases Cls Cm (lift_succ i) = Cls i.
Proof.
  esimp[succ_maxi_cases], cases i with i ilt, esimp,
  apply decidable.rec,
  { intro ilt', esimp[val_inj], apply concat,
    apply ap (fun x => eq.rec_on x _), esimp[eq_of_veq, rfl], reflexivity,
    have H : ilt = ilt', by apply is_prop.elim, cases H,
    have H' : is_prop.elim (lt_add_of_lt_right ilt 1) (lt_add_of_lt_right ilt 1) = idp,
      by apply is_prop.elim,
    krewrite H' },
  { intro a, exact absurd ilt a },
Defined.

Definition elim_succ_maxi_cases_maxi {C : fin (nat.succ n) -> Type}
  {Cls : forall j : fin n, C (lift_succ j)} {Cm : C maxi} :
  succ_maxi_cases Cls Cm maxi = Cm.
Proof.
  esimp[succ_maxi_cases, maxi],
  apply decidable.rec,
  { intro a, apply absurd a !nat.lt_irrefl },
  { intro a, esimp[val_inj], apply concat,
    have H : (le.antisymm (le_of_lt_succ (lt_succ_self n)) (le_of_not_gt a))^-1 = idp,
      by apply is_prop.elim,
    apply ap _ H, krewrite eq_of_veq_refl },
Defined.

Definition foldr {A B : Type} (m : A -> B -> B) (b : B) : forall {n : nat}, (fin n -> A) -> B.
  nat.rec (fun f => b) (fun n IH f => m (f (fin.zero n)) (IH (fun i : fin n => f (succ i))))

Definition foldl {A B : Type} (m : B -> A -> B) (b : B) : forall {n : nat}, (fin n -> A) -> B.
  nat.rec (fun f => b) (fun n IH f => m (IH (fun i : fin n => f (lift_succ i))) (f maxi))

Definition choice {C : fin n -> Type} :
  (forall i : fin n, nonempty (C i)) -> nonempty (forall i : fin n, C i).
Proof.
  revert C,
  induction n with [n, IH],
  { intros C H,
    apply nonempty.intro,
    exact elim0 },
  { intros C H,
    fapply nonempty.elim (H (fin.zero n)),
    intro CO,
    fapply nonempty.elim (IH (fun i => C (succ i)) (fun i => H (succ i))),
    intro CS,
    apply nonempty.intro,
    exact zero_succ_cases CO CS }
Defined.

(*section
open list
local postfix `+1`:100 . nat.succ

lemma dmap_map_lift {n : nat} : forall l : list nat, (forall i, i ∈ l -> i < n) -> dmap (fun i => i < n +1) mk l = map lift_succ (dmap (fun i => i < n) mk l)
| []     . assume Plt, rfl
| (i::l) . assume Plt, begin
  rewrite [@dmap_cons_of_pos _ _ (fun i => i < n +1) _ _ _ (lt_succ_of_lt (Plt i !mem_cons)), @dmap_cons_of_pos _ _ (fun i => i < n) _ _ _ (Plt i !mem_cons), map_cons],
  congruence,
  apply dmap_map_lift,
  intro j Pjinl, apply Plt, apply mem_cons_of_mem, assumption end

lemma upto_succ (n : nat) : upto (n +1) = maxi :: map lift_succ (upto n).
Proof.
  rewrite [↑fin.upto, list.upto_succ, @dmap_cons_of_pos _ _ (fun i => i < n +1) _ _ _ (nat.self_lt_succ n)],
  congruence,
  apply dmap_map_lift, apply @list.lt_of_mem_upto
Defined.

Definition upto_step : forall {n : nat}, fin.upto (n +1) = (map succ (upto n))++[0]
| 0      . rfl
| (i +1) . begin rewrite [upto_succ i, map_cons, append_cons, succ_max, upto_succ, -lift_zero],
  congruence, rewrite [map_map, -lift_succ.comm, -map_map, -(map_singleton _ 0), -map_append, -upto_step] end
Defined.*)

open sum equiv decidable

Definition fin_zero_equiv_empty : fin 0 <~> empty.
Proof.
  fapply equiv.MK, rotate 1, do 2 (intro x; contradiction),
  rotate 1, do 2 (intro x; apply elim0 x)
Defined.

Definition is_contr_fin_one [instance] : is_contr (fin 1).
Proof.
  fapply is_contr.mk, exact 0,
  intro x, induction x with v vlt,
  apply eq_of_veq, rewrite val_zero,
  apply inverse, apply eq_zero_of_le_zero, apply le_of_succ_le_succ, exact vlt,
Defined.

Definition fin_sum_equiv (n m : nat) : (fin n + fin m) <~> fin (n+m).
Proof.
  fapply equiv.MK,
  { intro s, induction s with l r,
    induction l with v vlt, apply mk v, apply lt_add_of_lt_right, exact vlt,
    induction r with v vlt, apply mk (v + n), rewrite {n + m}add.comm,
    apply add_lt_add_of_lt_of_le vlt, apply nat.le_refl },
  { intro f, induction f with v vlt,
    exact if h : v < n
          then sum.inl (mk v h)
          else sum.inr (mk (v-n) (nat.sub_lt_of_lt_add vlt (le_of_not_gt h))) },
  { intro f, cases f with v vlt, esimp, apply @by_cases (v < n),
    intro vltn, rewrite [dif_pos vltn], apply eq_of_veq, reflexivity,
    intro nvltn, rewrite [dif_neg nvltn], apply eq_of_veq, esimp,
    apply nat.sub_add_cancel, apply le_of_not_gt, apply nvltn },
  { intro s, cases s with f g,
    cases f with v vlt, rewrite [dif_pos vlt],
    cases g with v vlt, esimp, have ¬ v + n < n, from
      suppose v + n < n,
      have v < n - n, from nat.lt_sub_of_add_lt this !le.refl,
      have v < 0, by rewrite [nat.sub_self at this]; exact this,
      absurd this !not_lt_zero,
    apply concat, apply dif_neg this, apply ap inr, apply eq_of_veq, esimp,
    apply nat.add_sub_cancel },
Defined.

Definition fin_succ_equiv (n : nat) : fin (n + 1) <~> fin n + unit.
Proof.
  fapply equiv.MK,
  { apply succ_maxi_cases, esimp, apply inl, apply inr unit.star },
  { intro d, cases d, apply lift_succ a, apply maxi },
  { intro d, cases d,
    cases a with a alt, esimp, apply elim_succ_maxi_cases_lift_succ,
    cases a, apply elim_succ_maxi_cases_maxi },
  { intro a, apply succ_maxi_cases, esimp,
    intro j, krewrite elim_succ_maxi_cases_lift_succ,
    krewrite elim_succ_maxi_cases_maxi },
Defined.

open prod

Definition fin_prod_equiv (n m : nat) : (fin n \* fin m) <~> fin (n*m).
Proof.
  induction n,
  { krewrite nat.zero_mul,
    calc fin 0 \* fin m <~> empty \* fin m : fin_zero_equiv_empty
                   ... <~> fin m \* empty : prod_comm_equiv
                   ... <~> empty : prod_empty_equiv
                   ... <~> fin 0 : fin_zero_equiv_empty },
  { have H : (a + 1) * m = a * m + m, by rewrite [nat.right_distrib, one_mul],
    calc fin (a + 1) \* fin m
         <~> (fin a + unit) \* fin m : prod.prod_equiv_prod_right !fin_succ_equiv
     ... <~> (fin a \* fin m) + (unit \* fin m) : sum_prod_right_distrib
     ... <~> (fin a \* fin m) + (fin m \* unit) : prod_comm_equiv
     ... <~> fin (a * m) + (fin m \* unit) : v_0
     ... <~> fin (a * m) + fin m : prod_unit_equiv
     ... <~> fin (a * m + m) : fin_sum_equiv
     ... <~> fin ((a + 1) * m) : equiv_of_eq (ap fin H^-1) },
Defined.

Definition fin_two_equiv_bool : fin 2 <~> bool.
let H . equiv_unit_of_is_contr (fin 1) in
calc
  fin 2 <~> fin (1 + 1)   : equiv.refl
   ...  <~> fin 1 + fin 1 : fin_sum_equiv
   ...  <~> unit + unit   : H
   ...  <~> bool          : bool_equiv_unit_sum_unit

Definition fin_sum_unit_equiv (n : nat) : fin n + unit <~> fin (nat.succ n).
let H . equiv_unit_of_is_contr (fin 1) in
calc
  fin n + unit <~> fin n + fin 1 : H
          ...  <~> fin (nat.succ n)     : fin_sum_equiv

Definition fin_sum_equiv_cancel {n : nat} {A B : Type} (H : (fin n) + A <~> (fin n) + B) :
  A <~> B.
Proof.
  induction n with n IH,
  { calc A <~> A + empty : sum_empty_equiv
       ... <~> empty + A : sum_comm_equiv
       ... <~> fin 0 + A : fin_zero_equiv_empty
       ... <~> fin 0 + B : H
       ... <~> empty + B : fin_zero_equiv_empty
       ... <~> B + empty : sum_comm_equiv
       ... <~> B : sum_empty_equiv },
  { apply IH, apply unit_sum_equiv_cancel,
    calc unit + (fin n + A) <~> (unit + fin n) + A : sum_assoc_equiv
                        ... <~> (fin n + unit) + A : sum_comm_equiv
                        ... <~> fin (nat.succ n) + A : fin_sum_unit_equiv
                        ... <~> fin (nat.succ n) + B : H
                        ... <~> (fin n + unit) + B : fin_sum_unit_equiv
                        ... <~> (unit + fin n) + B : sum_comm_equiv
                        ... <~> unit + (fin n + B) : sum_assoc_equiv },
Defined.


Definition eq_of_fin_equiv {m n : nat} (H :fin m <~> fin n) : m = n.
Proof.
  revert n H, induction m with m IH IH,
  { intro n H, cases n, reflexivity, exfalso,
    apply to_fun fin_zero_equiv_empty => apply to_inv H, apply fin.zero },
  { intro n H, cases n with n, exfalso,
    apply to_fun fin_zero_equiv_empty => apply to_fun H => apply fin.zero,
    have unit + fin m <~> unit + fin n, from
    calc unit + fin m <~> fin m + unit : sum_comm_equiv
                  ... <~> fin (nat.succ m) : fin_succ_equiv
                  ... <~> fin (nat.succ n) : H
                  ... <~> fin n + unit : fin_succ_equiv
                  ... <~> unit + fin n : sum_comm_equiv,
    have fin m <~> fin n, from unit_sum_equiv_cancel this,
    apply ap nat.succ, apply IH _ this },
Defined.

Definition cyclic_succ {n : ℕ} (x : fin n) : fin n.
Proof.
    cases n with n,
    { exfalso, apply not_lt_zero _ (is_lt x)},
    { exact
      if H : val x = n
        then fin.mk 0 !zero_lt_succ
        else fin.mk (nat.succ (val x))
               (succ_lt_succ (lt_of_le_of_ne (le_of_lt_succ (is_lt x)) H))}
Defined.

Definition cyclic_pred {n : ℕ} (x : fin n) : fin n.
Proof.
    cases n with n,
    { exfalso, apply not_lt_zero _ (is_lt x)},
    { cases x with m H, cases m with m,
      { exact fin.mk n (self_lt_succ n) },
      { exact fin.mk m (lt.trans (self_lt_succ m) H) }}
Defined.

  (*
    We want to say that fin (succ n) always has a 0 and 1. However, we want a bit more, because
    sometimes we want a zero of (fin a) where a is either
    - equal to a successor, but notDefinitionally a successor (e.g. (0 : fin (3 + n)))
    -Definitionally equal to a successor, but not in a way that type class inference can infer.
      (e.g. (0 : fin 4). Note that 4 is bit0 (bit0 one), but (bit0 x) (defined as x + x),
        is not always a successor)
    To solve this we use an auxillary class `is_succ` which can solve whether a number is a
    successor.
  *)

  (* this is a version of `madd` which might compute better *)
  protectedDefinition add {n : ℕ} (x y : fin n) : fin n.
  iterate cyclic_succ (val y) x

Definition has_zero_fin [instance] (n : ℕ) [H : is_succ n] : has_zero (fin n).
  by induction H with n; exact has_zero.mk (fin.zero n)

Definition has_one_fin [instance] (n : ℕ) [H : is_succ n] : has_one (fin n).
  by induction H with n; exact has_one.mk (cyclic_succ (fin.zero n))

Definition has_add_fin [instance] (n : ℕ) : has_add (fin n).
  has_add.mk fin.add

Defined. fin
