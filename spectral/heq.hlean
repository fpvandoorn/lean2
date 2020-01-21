
open eq is_trunc

variables {I : Type} [is_set I] {P : I -> Type} {i j k : I} {x x₁ x₂ : P i} {y y₁ y₂ : P j} {z : P k}
  {Q : forall (i), P i -> Type}

structure heq (x : P i) (y : P j) : Type.
  (p : i = j)
  (q : x =[p] y)

namespace eq
notation x ` ==[`:50 P:0 `] `:0 y:50 . @heq _ _ P _ _ x y
infix ` == `:50 . heq
Definition pathover_of_heq {p : i = j} (q : x ==[P] y) : x =[p] y.
change_path !is_set.elim (heq.q q)

Definition eq_of_heq (p : x₁ ==[P] x₂) : x₁ = x₂.
eq_of_pathover_idp (pathover_of_heq p)

Definition heq.elim (p : x ==[P] y) (q : Q x) : Q y.
Proof.
  induction p with p r, induction r, exact q
Defined.

Definition heq.refl [refl] (x : P i) : x ==[P] x.
heq.mk idp idpo

Definition heq.rfl : x ==[P] x.
heq.refl x

Definition heq.symm [symm] (p : x ==[P] y) : y ==[P] x.
Proof.
  induction p with p q, constructor, exact q^-1ᵒ
Defined.

Definition heq_of_eq (p : x₁ = x₂) : x₁ ==[P] x₂.
heq.mk idp (pathover_idp_of_eq p)

Definition heq.trans [trans] (p : x ==[P] y) (p₂ : y ==[P] z) : x ==[P] z.
Proof.
  induction p with p q, induction p₂ with p₂ q₂, constructor, exact q @o q₂
Defined.

infix ` @he `:72 . heq.trans
postfix `^-1ʰᵉ`:(max+10) . heq.symm


Definition heq_of_heq_of_eq (p : x ==[P] y) (p₂ : y = y₂) : x ==[P] y₂.
p @he heq_of_eq p₂

Definition heq_of_eq_of_heq (p : x = x₂) (p₂ : x₂ ==[P] y) : x ==[P] y.
heq_of_eq p @he p₂

infix ` @hep `:73 . concato_eq
infix ` @phe `:74 . eq_concato

Definition heq_tr (p : i = j) (x : P i) : x ==[P] transport P p x.
heq.mk p !pathover_tr

Definition tr_heq (p : i = j) (x : P i) : transport P p x ==[P] x.
(heq_tr p x)^-1ʰᵉ

Defined. eq
