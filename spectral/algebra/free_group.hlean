(*
Copyright (c) 2015-2018 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke, Ulrik Buchholtz

Constructions with groups
*)

import algebra.group_theory hit.set_quotient types.list types.sum ..move_to_lib

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod sum list trunc function equiv
  prod.ops decidable is_equiv pointed

universe variable u

namespace group

  variables {G G' : Group} {g g' h h' k : G} {A B : AbGroup}

  (* Free Group of a pointed set *)
  variables (X : pType) [is_set X] {l l' : list (X ⊎ X)}
  namespace free_group

  inductive free_group_rel : list (X ⊎ X) -> list (X ⊎ X) -> Type.
  | rrefl   : forall l, free_group_rel l l
  | cancel1 : forall x, free_group_rel [inl x, inr x] []
  | cancel2 : forall x, free_group_rel [inr x, inl x] []
  | cancelpt1 : free_group_rel [inl (point _)] []
  | cancelpt2 : free_group_rel [inr (point _)] []
  | resp_append : forall {l₁ l₂ l₃ l₄}, free_group_rel l₁ l₂ -> free_group_rel l₃ l₄ ->
  free_group_rel (l₁ ++ l₃) (l₂ ++ l₄)
  | rtrans : forall {l₁ l₂ l₃}, free_group_rel l₁ l₂ -> free_group_rel l₂ l₃ ->
  free_group_rel l₁ l₃

  open free_group_rel
  local abbreviation R . free_group_rel
  attribute free_group_rel.rrefl [refl]

Definition free_group_carrier : Type . set_quotient (fun x y => ∥R X x y∥)
  local abbreviation FG . free_group_carrier

Definition is_reflexive_R : is_reflexive (fun x y => ∥R X x y∥).
Proof. constructor, intro s, apply tr, unfold R end
  local attribute is_reflexive_R [instance]

  variable {X}
Definition rel_respect_flip (r : R X l l') : R X (map sum.flip l) (map sum.flip l').
Proof.
  induction r with l x x l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂,
  { reflexivity},
  { repeat esimp [map], exact cancel2 x},
  { repeat esimp [map], exact cancel1 x},
  { exact cancelpt2 X },
  { exact cancelpt1 X },
  { rewrite [+map_append], exact resp_append IH₁ IH₂},
  { exact rtrans IH₁ IH₂}
Defined.

Definition rel_respect_reverse (r : R X l l') : R X (reverse l) (reverse l').
Proof.
  induction r with l x x l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂,
  { reflexivity},
  { repeat esimp [map], exact cancel2 x},
  { repeat esimp [map], exact cancel1 x},
  { exact cancelpt1 X },
  { exact cancelpt2 X },
  { rewrite [+reverse_append], exact resp_append IH₂ IH₁},
  { exact rtrans IH₁ IH₂}
Defined.

Definition free_group_one : FG X . class_of []
Definition free_group_inv : FG X -> FG X.
  quotient_unary_map (reverse o map sum.flip)
  (fun l l' => trunc_functor -1 (rel_respect_reverse o rel_respect_flip))
Definition free_group_mul [unfold 3 4] : FG X -> FG X -> FG X.
  quotient_binary_map append (fun l l' => trunc.elim (fun r m m' => trunc.elim (fun s => tr (resp_append r s))))

  section
  local notation 1 . free_group_one
  local postfix ^-1 . free_group_inv
  local infix * . free_group_mul

Definition free_group_mul_assoc (g₁ g₂ g₃ : FG X) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃).
Proof.
  refine set_quotient.rec_prop _ g₁,
  refine set_quotient.rec_prop _ g₂,
  refine set_quotient.rec_prop _ g₃,
  clear g₁ g₂ g₃, intro g₁ g₂ g₃,
  exact ap class_of !append.assoc
Defined.

Definition free_group_one_mul (g : FG X) : 1 * g = g.
Proof.
  refine set_quotient.rec_prop _ g, clear g, intro g,
  exact ap class_of !append_nil_left
Defined.

Definition free_group_mul_one (g : FG X) : g * 1 = g.
Proof.
  refine set_quotient.rec_prop _ g, clear g, intro g,
  exact ap class_of !append_nil_right
Defined.

Definition free_group_mul_left_inv (g : FG X) : g^-1 * g = 1.
Proof.
  refine set_quotient.rec_prop _ g, clear g, intro g,
  apply eq_of_rel, apply tr,
  induction g with s l IH,
  { reflexivity},
  { rewrite [▸*, map_cons, reverse_cons, concat_append],
  refine rtrans _ IH,
  apply resp_append, reflexivity,
  change R X ([flip s, s] ++ l) ([] ++ l),
  apply resp_append,
  induction s, apply cancel2, apply cancel1,
  reflexivity}
Defined.

Defined.
Defined. free_group open free_group
(*  export [reduce_hints] free_group *)
  variables (X)
Definition group_free_group : group (free_group_carrier X).
  group.mk _ free_group_mul free_group_mul_assoc free_group_one free_group_one_mul
  free_group_mul_one free_group_inv free_group_mul_left_inv

Definition free_group : Group.
  Group.mk _ (group_free_group X)

  (* The universal property of the free group *)
  variables {X G}
Definition free_group_inclusion : X ->* free_group X.
  ppi.mk (fun x => class_of [inl x]) (eq_of_rel (tr (free_group_rel.cancelpt1 X)))

Definition fgh_helper (f : X -> G) (g : G) (x : X ⊎ X) : G.
  g * sum.rec (fun z => f z) (fun z => (f z)^-1) x

Definition fgh_helper_respect_rel (f : X ->* G) (r : free_group_rel X l l')
  : forall (g : G), foldl (fgh_helper f) g l = foldl (fgh_helper f) g l'.
Proof.
  induction r with l x x l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂: intro g,
  { reflexivity},
  { unfold [foldl], apply mul_inv_cancel_right},
  { unfold [foldl], apply inv_mul_cancel_right},
  { unfold [foldl], rewrite (point_eq f), apply mul_one },
  { unfold [foldl], rewrite [point_eq f, one_inv], apply mul_one },
  { rewrite [+foldl_append, IH₁, IH₂]},
  { exact !IH₁ @ !IH₂}
Defined.

Definition fgh_helper_mul (f : X -> G) (l)
  : forall (g : G), foldl (fgh_helper f) g l = g * foldl (fgh_helper f) 1 l.
Proof.
  induction l with s l IH: intro g,
  { unfold [foldl], exact !mul_one^-1},
  { rewrite [+foldl_cons, IH], refine _ @ (ap (fun x => g * x) !IH^-1),
  rewrite [-mul.assoc, ↑fgh_helper, one_mul]}
Defined.

Definition free_group_hom (f : X ->* G) : free_group X ->g G.
Proof.
  fapply homomorphism.mk,
  { intro g, refine set_quotient.elim _ _ g,
  { intro l, exact foldl (fgh_helper f) 1 l},
  { intro l l' r, esimp at *, refine trunc.rec _ r, clear r, intro r,
  exact fgh_helper_respect_rel f r 1}},
  { refine set_quotient.rec_prop _, intro l, refine set_quotient.rec_prop _, intro l',
  esimp, refine !foldl_append @ _, esimp, apply fgh_helper_mul}
Defined.

Definition free_group_hom_eq {φ ψ : free_group X ->g G}
  (H : forall x, φ (free_group_inclusion x) = ψ (free_group_inclusion x)) : φ == ψ.
Proof.
  refine set_quotient.rec_prop _, intro l,
  induction l with s l IH,
  { exact respect_one φ @ (respect_one ψ)^-1 },
  { refine respect_mul φ (class_of [s]) (class_of l) @ _ @
  (respect_mul ψ (class_of [s]) (class_of l))^-1,
  refine ap011 mul _ IH, induction s with x x, exact H x,
  refine respect_inv φ (class_of [inl x]) @ ap inv (H x) @
  (respect_inv ψ (class_of [inl x]))^-1 }
Defined.

Definition fn_of_free_group_hom [unfold_full] (φ : free_group X ->g G) : X ->* G.
  ppi.mk (φ o free_group_inclusion)
Proof.
  refine (_ @ respect_one φ),
  apply ap φ, apply eq_of_rel, apply tr,
  exact (free_group_rel.cancelpt1 X)
Defined.

  variables (X G)
Definition free_group_hom_equiv_fn : (free_group X ->g G) <~> (X ->* G).
Proof.
  fapply equiv.MK,
  { exact fn_of_free_group_hom},
  { exact free_group_hom},
  { intro f, apply path_pforall, fapply Build_pHomotopy,
  { intro x, esimp, unfold [foldl], apply one_mul },
  { apply is_prop.elim } },
  { intro φ, apply homomorphism_eq, apply free_group_hom_eq, intro x, apply one_mul }
Defined.

Defined. group

(* alternativeDefinition of free group on a set with decidable equality *)

namespace list

variables {X : Type.{u}} {v w : X ⊎ X} {l : list (X ⊎ X)}

inductive is_reduced {X : Type} : list (X ⊎ X) -> Type.
| nil       : is_reduced []
| singleton : forall v, is_reduced [v]
| cons      : forall (v w l), sum.flip v ≠ w -> is_reduced (w::l) -> is_reduced (v::w::l)

Definition is_reduced_code (H : is_reduced l) : Type.{u}.
Proof.
  cases l with v l, { exact is_reduced.nil = H },
  cases l with w l, { exact is_reduced.singleton v = H },
  exact Σ(pH : sum.flip v ≠ w \* is_reduced (w::l)), is_reduced.cons pH.1 pH.2 = H
Defined.

Definition is_reduced_encode (H : is_reduced l) : is_reduced_code H.
Proof.
  induction H with v v w l p Hl IH,
  { exact idp },
  { exact idp },
  { exact ⟨(p, Hl), idp⟩ }
Defined.

Definition is_prop_is_reduced (l : list (X ⊎ X)) : is_prop (is_reduced l).
Proof.
  apply is_prop.mk, intro H₁ H₂, induction H₁ with v v w l p Hl IH,
  { exact is_reduced_encode H₂ },
  { exact is_reduced_encode H₂ },
  { cases is_reduced_encode H₂ with pH' q, cases pH' with p' Hl', esimp at q,
  subst q, exact ap011 (fun x y => is_reduced.cons x y) !is_prop.elim (IH Hl') }
Defined.

Definition rlist (X : Type) : Type.
Σ(l : list (X ⊎ X)), is_reduced l

local attribute [instance] is_prop_is_reduced
Definition rlist_eq {l l' : rlist X} (p : l.1 = l'.1) : l = l'.
subtype_eq p

Definition is_trunc_rlist {n : ℕ₋₂} {X : Type} (H : is_trunc (n.+2) X) :
  is_trunc (n.+2) (rlist X).
Proof.
  apply is_trunc_sigma, { apply is_trunc_list, apply is_trunc_sum },
  intro l, exact is_trunc_succ_of_is_prop _ _ _
Defined.

Definition is_reduced_invert (v : X ⊎ X) : is_reduced (v::l) -> is_reduced l.
Proof.
  assert H : forall (l'), is_reduced l' -> l' = v::l -> is_reduced l,
  { intro l' Hl', revert l, induction Hl' with v' v' w' l' p' Hl' IH: intro l p,
  { cases p },
  { cases cons_eq_cons p with q r, subst r, apply is_reduced.nil },
  { cases cons_eq_cons p with q r, subst r, exact Hl' }},
  intro Hl, exact H Hl idp
Defined.

Definition is_reduced_invert_rev (v : X ⊎ X) : is_reduced (l++[v]) -> is_reduced l.
Proof.
  assert H : forall (l'), is_reduced l' -> l' = l++[v] -> is_reduced l,
  { intro l' Hl', revert l, induction Hl' with v' v' w' l' p' Hl' IH: intro l p,
  { induction l: cases p },
  { induction l with v'' l IH, apply is_reduced.nil, esimp [append] at p,
  cases cons_eq_cons p with q r, induction l: cases r },
  { induction l with v'' l IH', cases p, induction l with v''' l IH'',
  apply is_reduced.singleton, do 2 esimp [append] at p, cases cons_eq_cons p with q r,
  cases cons_eq_cons r with r₁ r₂, subst r₁, subst q, subst r₂,
  apply is_reduced.cons p' (IH _ idp) }},
  intro Hl, exact H Hl idp
Defined.

Definition rnil : rlist X.
⟨[], !is_reduced.nil⟩

Definition rsingleton (x : X ⊎ X) : rlist X.
⟨[x], !is_reduced.singleton⟩

Definition is_reduced_doubleton {x y : X ⊎ X} (p : flip x ≠ y) :
  is_reduced [x, y].
is_reduced.cons p !is_reduced.singleton

Definition rdoubleton {x y : X ⊎ X} (p : flip x ≠ y) : rlist X.
⟨[x, y], is_reduced_doubleton p⟩

Definition is_reduced_concat (Hn : sum.flip v ≠ w) (Hl : is_reduced (concat v l)) :
  is_reduced (concat w (concat v l)).
Proof.
  assert H : forall (l'), is_reduced l' -> l' = concat v l -> is_reduced (concat w l'),
  { clear Hl, intro l' Hl', revert l, induction Hl' with v' v' w' l' p' Hl' IH: intro l p,
  { exfalso, exact concat_neq_nil _ _ p^-1 },
  { cases concat_eq_singleton p^-1 with q r, subst q,
  exact is_reduced_doubleton Hn },
  { do 2 esimp [concat], apply is_reduced.cons p', cases l with x l,
  { cases p },
  { apply IH l, esimp [concat] at p, revert p, generalize concat v l, intro l'' p,
  cases cons_eq_cons p with q r, exact r }}},
  exact H Hl idp
Defined.

Definition is_reduced_reverse (H : is_reduced l) : is_reduced (reverse l).
Proof.
  induction H with v v w l p Hl IH,
  { apply is_reduced.nil },
  { apply is_reduced.singleton },
  { refine is_reduced_concat _ IH, intro q, apply p, subst q, apply flip_flip }
Defined.

Definition rreverse (l : rlist X) : rlist X . ⟨reverse l.1, is_reduced_reverse l.2⟩

Definition rreverse_rreverse (l : rlist X) : rreverse (rreverse l) = l.
subtype_eq (reverse_reverse l.1)

Definition is_reduced_flip (H : is_reduced l) : is_reduced (map flip l).
Proof.
  induction H with v v w l p Hl IH,
  { apply is_reduced.nil },
  { apply is_reduced.singleton },
  { refine is_reduced.cons _ IH, intro q, apply p, exact !flip_flip^-1 @ ap flip q @ !flip_flip }
Defined.

Definition rflip (l : rlist X) : rlist X . ⟨map flip l.1, is_reduced_flip l.2⟩

Definition rcons' [decidable_eq X] (v : X ⊎ X) (l : list (X ⊎ X)) : list (X ⊎ X).
Proof.
  cases l with w l,
  { exact [v] },
  { exact if q : sum.flip v = w then l else v::w::l }
Defined.

Definition is_reduced_rcons [decidable_eq X] (v : X ⊎ X) (Hl : is_reduced l) :
  is_reduced (rcons' v l).
Proof.
  cases l with w l, apply is_reduced.singleton,
  apply dite (sum.flip v = w): intro q,
  { have is_set (X ⊎ X), from !is_trunc_sum,
  rewrite [↑rcons', dite_true q _], exact is_reduced_invert w Hl },
  { rewrite [↑rcons', dite_false q], exact is_reduced.cons q Hl, }
Defined.

Definition rcons [decidable_eq X] (v : X ⊎ X) (l : rlist X) : rlist X.
⟨rcons' v l.1, is_reduced_rcons v l.2⟩

Definition rcons_eq [decidable_eq X] : is_reduced (v::l) -> rcons' v l = v :: l.
Proof.
  assert H : forall (l'), is_reduced l' -> l' = v::l -> rcons' v l = l',
  { intro l' Hl', revert l, induction Hl' with v' v' w' l' p' Hl' IH: intro l p,
  { cases p },
  { cases cons_eq_cons p with q r, subst r, cases p, reflexivity },
  { cases cons_eq_cons p with q r, subst q, subst r, rewrite [↑rcons', dite_false p'], }},
  intro Hl, exact H Hl idp
Defined.

Definition rcons_eq2 [decidable_eq X] (H : is_reduced (v::l)) :
  ⟨v :: l, H⟩ = rcons v ⟨l, is_reduced_invert _ H⟩.
subtype_eq (rcons_eq H)^-1

Definition rcons_rcons_eq [decidable_eq X] (p : flip v = w) (l : rlist X) :
  rcons v (rcons w l) = l.
Proof.
  have is_set (X ⊎ X), from !is_trunc_sum,
  induction l with l Hl,
  apply rlist_eq, esimp,
  induction l with u l IH,
  { exact dite_true p _ },
  { apply dite (sum.flip w = u): intro q,
  { rewrite [↑rcons' at {1}, dite_true q _], subst p, induction (!flip_flip^-1 @ q),
  exact rcons_eq Hl },
  { rewrite [↑rcons', dite_false q, dite_true p _] }}
Defined.

Definition rlist.rec [decidable_eq X] {P : rlist X -> Type}
  (P1 : P rnil) (Pcons : forall v l, P l -> P (rcons v l)) (l : rlist X) : P l.
Proof.
  induction l with l Hl, induction Hl with v v w l p Hl IH,
  { exact P1 },
  { exact Pcons v rnil P1 },
  { exact transport P (subtype_eq (rcons_eq (is_reduced.cons p Hl))) (Pcons v ⟨w :: l, Hl⟩ IH) }
Defined.

Definition reduce_list' [decidable_eq X] (l : list (X ⊎ X)) : list (X ⊎ X).
Proof.
  induction l with v l IH,
  { exact [] },
  { exact rcons' v IH }
Defined.

Definition is_reduced_reduce_list [decidable_eq X] (l : list (X ⊎ X)) :
  is_reduced (reduce_list' l).
Proof.
  induction l with v l IH, apply is_reduced.nil,
  apply is_reduced_rcons, exact IH
Defined.

Definition reduce_list [decidable_eq X] (l : list (X ⊎ X)) : rlist X.
⟨reduce_list' l, is_reduced_reduce_list l⟩

Definition rappend' [decidable_eq X] (l : list (X ⊎ X)) (l' : rlist X) : rlist X . foldr rcons l' l
Definition rappend_rcons' [decidable_eq X] (x : X ⊎ X) (l₁ : list (X ⊎ X)) (l₂ : rlist X) :
  rappend' (rcons' x l₁) l₂ = rcons x (rappend' l₁ l₂).
Proof.
  induction l₁ with x' l₁ IH,
  { reflexivity },
  { apply dite (sum.flip x = x'): intro p,
  { have is_set (X ⊎ X), from !is_trunc_sum, rewrite [↑rcons', dite_true p _],
  exact (rcons_rcons_eq p _)^-1 },
  { rewrite [↑rcons', dite_false p] }}
Defined.

Definition rappend_cons' [decidable_eq X] (x : X ⊎ X) (l₁ : list (X ⊎ X)) (l₂ : rlist X) :
  rappend' (x::l₁) l₂ = rcons x (rappend' l₁ l₂).
idp

Definition rappend [decidable_eq X] (l l' : rlist X) : rlist X . rappend' l.1 l'

Definition rappend_rcons [decidable_eq X] (x : X ⊎ X) (l₁ l₂ : rlist X) :
  rappend (rcons x l₁) l₂ = rcons x (rappend l₁ l₂).
rappend_rcons' x l₁.1 l₂

Definition rappend_assoc [decidable_eq X] (l₁ l₂ l₃ : rlist X) :
  rappend (rappend l₁ l₂) l₃ = rappend l₁ (rappend l₂ l₃).
Proof.
  induction l₁ with l₁ h, unfold rappend, clear h, induction l₁ with x l₁ IH,
  { reflexivity },
  { rewrite [rappend_cons', ▸*, rappend_rcons', IH] }
Defined.

Definition rappend_rnil [decidable_eq X] (l : rlist X) : rappend l rnil = l.
Proof.
  induction l with l H, apply rlist_eq, esimp, induction H with v v w l p Hl IH,
  { reflexivity },
  { reflexivity },
  { rewrite [↑rappend at *, rappend_cons', ↑rcons, IH, ↑rcons', dite_false p] }
Defined.

Definition rnil_rappend [decidable_eq X] (l : rlist X) : rappend rnil l = l.
by reflexivity

Definition rsingleton_rappend [decidable_eq X] (x : X ⊎ X) (l : rlist X) :
  rappend (rsingleton x) l = rcons x l.
by reflexivity

Definition rappend_left_inv [decidable_eq X] (l : rlist X) :
  rappend (rflip (rreverse l)) l = rnil.
Proof.
  induction l with l H, apply rlist_eq, induction l with x l IH,
  { reflexivity },
  { have is_set (X ⊎ X), from !is_trunc_sum,
  rewrite [↑rappend, ↑rappend', reverse_cons, map_concat, foldr_concat],
  refine ap (fun x => (rappend' _ x).1) (rlist_eq (dite_true !flip_flip _)) @
  IH (is_reduced_invert _ H) }
Defined.

Definition rappend'_eq [decidable_eq X] (v : X ⊎ X) (l : list (X ⊎ X)) (H : is_reduced (l ++ [v])) :
  ⟨l ++ [v], H⟩ = rappend' l (rsingleton v).
Proof.
  assert Hlem : forall (l') (Hl' : is_reduced l'), l' = l ++ [v] -> rappend' l (rsingleton v) = ⟨l', Hl'⟩,
  { intro l' Hl', clear H, revert l,
  induction Hl' with v' v' w' l' p' Hl' IH: intro l p,
  { induction l: cases p },
  { induction l with v'' l IH,
  { cases cons_eq_cons p with q r, subst q },
  { esimp [append] at p, cases cons_eq_cons p with q r, induction l: cases r }},
  { induction l with v'' l IH', cases p,
  induction l with v''' l IH'',
  { do 2 esimp [append] at p, cases cons_eq_cons p with q r, subst q,
  cases cons_eq_cons r with q r', subst q, subst r', apply subtype_eq, exact dite_false p' },
  { do 2 esimp [append] at p, cases cons_eq_cons p with q r,
  cases cons_eq_cons r with r₁ r₂, subst r₁, subst q, subst r₂,
  rewrite [rappend_cons', IH (w' :: l) idp],
  apply subtype_eq, apply rcons_eq, apply is_reduced.cons p' Hl' }}},
  exact (Hlem H idp)^-1
Defined.

Definition rappend_eq [decidable_eq X] (v : X ⊎ X) (l : list (X ⊎ X)) (H : is_reduced (l ++ [v])) :
  ⟨l ++ [v], H⟩ = rappend ⟨l, is_reduced_invert_rev _ H⟩ (rsingleton v).
rappend'_eq v l H

Definition rreverse_cons [decidable_eq X] (v : X ⊎ X) (l : list (X ⊎ X))
  (H : is_reduced (v :: l)) : rreverse ⟨v::l, H⟩ =
  rappend ⟨reverse l, is_reduced_reverse (is_reduced_invert _ H)⟩ (rsingleton v).
Proof.
  refine dpair_eq_dpair (reverse_cons _ _) !pathover_tr @ _,
  refine dpair_eq_dpair (concat_eq_append _ _) !pathover_tr @ _,
  refine !rappend_eq @ _,
  exact ap (fun x => rappend ⟨_, x⟩ _) !is_prop.elim
Defined.

Definition rreverse_rcons [decidable_eq X] (v : X ⊎ X) (l : rlist X) :
  rreverse (rcons v l) = rappend (rreverse l) (rsingleton v).
Proof.
  induction l with l Hl, induction l with v' l IH, reflexivity,
  { symmetry, refine ap (fun x => rappend x _) !rreverse_cons @ _,
  apply dite (sum.flip v = v'): intro p,
  { have is_set (X ⊎ X), from !is_trunc_sum,
  rewrite [↑rcons, ↑rcons', dpair_eq_dpair (dite_true p _) !pathover_tr ],
  refine !rappend_assoc @ _, refine ap (rappend _) !rsingleton_rappend @ _,
  refine ap (rappend _) (subtype_eq _) @ !rappend_rnil,
  exact dite_true (ap flip p^-1 @ flip_flip v) _ },
  { rewrite [↑rcons, ↑rcons', dpair_eq_dpair (dite_false p) !pathover_tr],
  note H1 . is_reduced_reverse (transport is_reduced (dite_false p) (is_reduced_rcons v Hl)),
  rewrite [+reverse_cons at H1, +concat_eq_append at H1],
  note H2 . is_reduced_invert_rev _ H1,
  refine ap (fun x => rappend x _) (rappend_eq _ _ H2)^-1 @ _,
  refine (rappend_eq _ _ H1)^-1 @ _, apply subtype_eq,
  rewrite [-+concat_eq_append] }}

Defined.

Definition rlist.rec_rev [decidable_eq X] {P : rlist X -> Type}
  (P1 : P rnil) (Pappend : forall l v, P l -> P (rappend l (rsingleton v))) : forall (l : rlist X), P l.
Proof.
  assert H : forall (l : rlist X), P (rreverse l),
  { refine rlist.rec _ _, exact P1, intro v l p,
  rewrite [rreverse_rcons], apply Pappend, exact p },
  intro l, exact transport P (rreverse_rreverse l) (H (rreverse l))
Defined.

Defined. list open list

namespace group
  open sigma.ops

  variables (X : Type) [decidable_eq X] {G : InfGroup}
Definition group_dfree_group : group (rlist X).
  group.mk (is_trunc_rlist _) rappend rappend_assoc rnil rnil_rappend rappend_rnil
  (rflip o rreverse) rappend_left_inv

Definition dfree_group : Group.
  Group.mk _ (group_dfree_group X)

  variable {X}
Definition dfree_group_inclusion (x : X) : dfree_group X.
  rsingleton (inl x)

Definition rsingleton_inr (x : X) :
  rsingleton (inr x) = (dfree_group_inclusion x)^-1 :> dfree_group X.
  by reflexivity

  local attribute [instance] is_prop_is_reduced
Definition dfree_group.rec {P : dfree_group X -> Type}
  (P1 : P 1) (Pcons : forall v g, P g -> P (rsingleton v * g)) : forall (g : dfree_group X), P g.
  rlist.rec P1 Pcons

Definition dfree_group.rec_rev {P : dfree_group X -> Type}
  (P1 : P 1) (Pcons : forall g v, P g -> P (g * rsingleton v)) : forall (g : dfree_group X), P g.
  rlist.rec_rev P1 Pcons

  (*Definition dfree_group.rec2 {P : dfree_group X -> Type} *)
  (*   (P1 : P 1) (Pcons : forall g x, P g -> P (dfree_group_inclusion x * g)) *)
  (*   (Pinv : forall g, P g -> P g^-1) : forall (g : dfree_group X), P g . *)
  (* begin *)
  (*   refine dfree_group.rec _ _, exact P1, *)
  (*   intro g v p, induction v with x x, exact Pcons g x p, *)

  (* end *)

Definition dfgh_helper (f : X -> G) (g : G) (x : X ⊎ X) : G.
  g * sum.rec (fun x => f x) (fun x => (f x)^-1) x

Definition dfgh_helper_mul (f : X -> G) (l : list (X ⊎ X))
  : forall (g : G), foldl (dfgh_helper f) g l = g * foldl (dfgh_helper f) 1 l.
Proof.
  induction l with s l IH: intro g,
  { unfold [foldl], exact !mul_one^-1},
  { rewrite [+foldl_cons, IH], refine _ @ (ap (fun x => g * x) !IH^-1),
  rewrite [-mul.assoc, ↑dfgh_helper, one_mul] }
Defined.

Definition dfgh_helper_rcons (f : X -> G) (g : G) (x : X ⊎ X) {l : list (X ⊎ X)} :
  foldl (dfgh_helper f) g (rcons' x l) = foldl (dfgh_helper f) g (x :: l).
Proof.
  cases l with x' l, reflexivity,
  apply dite (sum.flip x = x'): intro q,
  { have is_set (X ⊎ X), from !is_trunc_sum,
  rewrite [↑rcons', dite_true q _, foldl_cons, foldl_cons, -q],
  induction x with x, rewrite [↑dfgh_helper,mul_inv_cancel_right],
  rewrite [↑dfgh_helper,inv_mul_cancel_right] },
  { rewrite [↑rcons', dite_false q] }
Defined.

Definition dfgh_helper_rappend (f : X -> G) (g : G) (l l' : rlist X) :
  foldl (dfgh_helper f) g (rappend l l').1 = foldl (dfgh_helper f) g (l.1 ++ l'.1).
Proof.
  revert g, induction l with l lH, unfold rappend, clear lH,
  induction l with v l IH: intro g, reflexivity,
  rewrite [rappend_cons', ↑rcons, dfgh_helper_rcons, foldl_cons, IH]
Defined.

  local attribute [coercion] InfGroup_of_Group
Definition dfree_group_inf_hom (G : InfGroup) (f : X -> G) : dfree_group X ->∞g G.
  inf_homomorphism.mk (fun x => foldl (dfgh_helper f) 1 x.1)
  (fun l₁ l₂ => !dfgh_helper_rappend @ !foldl_append @ !dfgh_helper_mul)

Definition dfree_group_inf_hom_eq {G : InfGroup} {φ ψ : dfree_group X ->∞g G}
  (H : forall x, φ (dfree_group_inclusion x) = ψ (dfree_group_inclusion x)) : φ == ψ.
Proof.
  assert H2 : forall v, φ (rsingleton v) = ψ (rsingleton v),
  { intro v, induction v with x x, exact H x,
  exact to_respect_inv_inf φ _ @ ap inv (H x) @ (to_respect_inv_inf ψ _)^-1 },
  refine dfree_group.rec _ _,
  { exact !to_respect_one_inf @ !to_respect_one_inf^-1 },
  { intro v g p, exact !to_respect_mul_inf @ ap011 mul (H2 v) p @ !to_respect_mul_inf^-1 }
Defined.

Definition dfree_group_inf_hom_inclusion (G : InfGroup) (f : X -> G) (x : X) :
  dfree_group_inf_hom G f (dfree_group_inclusion x) = f x.
  by rewrite [▸*, foldl_cons, foldl_nil, ↑dfgh_helper, one_mul]

Definition dfree_group_hom {G : Group} (f : X -> G) : dfree_group X ->g G.
  homomorphism_of_inf_homomorphism (dfree_group_inf_hom G f)

  (* todo: use the inf-version *)
Definition dfree_group_hom_eq {G : Group} {φ ψ : dfree_group X ->g G}
  (H : forall x, φ (dfree_group_inclusion x) = ψ (dfree_group_inclusion x)) : φ == ψ.
Proof.
  assert H2 : forall v, φ (rsingleton v) = ψ (rsingleton v),
  { intro v, induction v with x x, exact H x,
  exact to_respect_inv φ _ @ ap inv (H x) @ (to_respect_inv ψ _)^-1 },
  refine dfree_group.rec _ _,
  { exact !to_respect_one @ !to_respect_one^-1 },
  { intro v g p, exact !to_respect_mul @ ap011 mul (H2 v) p @ !to_respect_mul^-1 }
Defined.

Definition is_mul_hom_dfree_group_fun {G : InfGroup} {f : dfree_group X -> G}
  (H1 : f 1 = 1) (H2 : forall v g, f (rsingleton v * g) = f (rsingleton v) * f g) : is_mul_hom f.
Proof.
  refine dfree_group.rec _ _,
  { intro g, exact ap f (one_mul g) @ (ap (fun x => x * _) H1 @ one_mul (f g))^-1 },
  { intro g v p h,
  exact ap f !mul.assoc @ !H2 @ ap (mul _) !p @ (ap (fun x => x * _) !H2 @ !mul.assoc)^-1 }
Defined.

Definition dfree_group_hom_of_fun {G : InfGroup} (f : dfree_group X -> G)
  (H1 : f 1 = 1) (H2 : forall v g, f (rsingleton v * g) = f (rsingleton v) * f g) :
  dfree_group X ->∞g G.
  inf_homomorphism.mk f (is_mul_hom_dfree_group_fun H1 H2)

  variable (X)

  open option

Definition free_group_of_dfree_group : dfree_group X ->g free_group X₊.
  dfree_group_hom (free_group_inclusion o some)

Definition dfree_group_of_free_group : free_group X₊ ->g dfree_group X.
  free_group_hom (ppi.mk (option.rec 1 dfree_group_inclusion) idp)

Definition dfree_group_isomorphism : dfree_group X <~>g free_group X₊.
Proof.
  apply isomorphism.MK (free_group_of_dfree_group X) (dfree_group_of_free_group X),
  { apply free_group_hom_eq, intro x, induction x with x,
  { symmetry, apply eq_of_rel, apply tr, exact free_group.free_group_rel.cancelpt1 X₊ },
  { reflexivity } },
  { apply dfree_group_hom_eq, intro x, reflexivity }
Defined.

Defined. group
