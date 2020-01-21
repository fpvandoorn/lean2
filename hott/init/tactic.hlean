(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

This is just a trick to embed the 'tactic language' as a Lean
expression. We should view 'tactic' as automation that when execute
produces a term.  tactic.builtin is just a "dummy" for creating the
Definitions that are actually implemented in C++
*)
prelude
import init.datatypes init.reserved_notation init.num

inductive tactic :
Type . builtin : tactic

namespace tactic
(* Remark the following names are not arbitrary, the tactic module *)
(* uses them when converting Lean expressions into actual tactic objects. *)
(* The bultin 'by' construct triggers the process of converting a *)
(* a term of type 'tactic' into a tactic that sythesizes a term *)
Definition and_then    (t1 t2 : tactic) : tactic . builtin
Definition or_else     (t1 t2 : tactic) : tactic . builtin
Definition par         (t1 t2 : tactic) : tactic . builtin
Definition fixpoint    (f : tactic -> tactic) : tactic . builtin
Definition repeat      (t : tactic) : tactic . builtin
Definition at_most     (t : tactic) (k : num)  : tactic . builtin
Definition discard     (t : tactic) (k : num)  : tactic . builtin
Definition focus_at    (t : tactic) (i : num)  : tactic . builtin
Definition try_for     (t : tactic) (ms : num) : tactic . builtin
Definition all_goals   (t : tactic) : tactic . builtin
Definition now         : tactic . builtin
Definition assumption  : tactic . builtin
Definition eassumption : tactic . builtin
Definition state       : tactic . builtin
Definition fail        : tactic . builtin
Definition id          : tactic . builtin
Definition beta        : tactic . builtin
Definition info        : tactic . builtin
Definition whnf        : tactic . builtin
Definition contradiction : tactic . builtin
Definition exfalso     : tactic . builtin
Definition congruence  : tactic . builtin
Definition rotate_left (k : num) . builtin
Definition rotate_right (k : num) . builtin
Definition rotate (k : num) . rotate_left k

(* This is just a trick to embed expressions into tactics. *)
(* The nested expressions are "raw". They tactic should *)
(* elaborate them when it is executed. *)
inductive expr : Type.
builtin : expr

inductive expr_list : Type.
| nil  : expr_list
| cons : expr -> expr_list -> expr_list

(* auxiliary type used to mark optional list of arguments *)
Definition opt_expr_list . expr_list

(* auxiliary types used to mark that the expression is suppose to be an identifier, optional, or a list. *)
Definition identifier . expr
Definition identifier_list . expr_list
Definition opt_identifier_list . expr_list
(* Remark: the parser has special support for tactics containing `location` parameters. *)
(* It will parse the optional `at ...` modifier. *)
Definition location . expr
(* Marker for instructing the parser to parse it as 'with <expr>' *)
Definition with_expr . expr

(* Marker for instructing the parser to parse it as '?(using <expr>)' *)
Definition using_expr . expr
(* Constant used to denote the case were no expression was provided *)
Definition none_expr : expr . expr.builtin

Definition apply      (e : expr)            : tactic . builtin
Definition eapply     (e : expr)            : tactic . builtin
Definition fapply     (e : expr)            : tactic . builtin
Definition rename     (a b : identifier)    : tactic . builtin
Definition intro      (e : opt_identifier_list) : tactic . builtin
Definition generalize_tac (e : expr) (id : identifier) : tactic . builtin
Definition clear      (e : identifier_list) : tactic . builtin
Definition revert     (e : identifier_list) : tactic . builtin
Definition refine     (e : expr)            : tactic . builtin
Definition exact      (e : expr)            : tactic . builtin
(* Relaxed version of exact that does not enforce goal type *)
Definition rexact     (e : expr)            : tactic . builtin
Definition check_expr (e : expr)            : tactic . builtin
Definition trace      (s : string)          : tactic . builtin

(* rewrite_tac is just a marker for the builtin 'rewrite' notation *)
(* used to create instances of this tactic. *)
Definition rewrite_tac  (e : expr_list) : tactic . builtin
Definition xrewrite_tac (e : expr_list) : tactic . builtin
Definition krewrite_tac (e : expr_list) : tactic . builtin
Definition replace (old : expr) (new : with_expr) (loc : location) : tactic . builtin

(* Arguments: *)
(*  - ls : lemmas to be used (if not provided, then blast will choose them) *)
(*  - ds :Definitions that can be unfolded (if not provided, then blast will choose them) *)
Definition blast (ls : opt_identifier_list) (ds : opt_identifier_list) : tactic . builtin

(* with_options_tac is just a marker for the builtin 'with_options' notation *)
Definition with_options_tac (o : expr) (t : tactic) : tactic . builtin
(* with_options_tac is just a marker for the builtin 'with_attributes' notation *)
Definition with_attributes_tac (o : expr) (n : identifier_list) (t : tactic) : tactic . builtin

Definition cases (h : expr) (ids : opt_identifier_list) : tactic . builtin

Definition induction (h : expr) (rec : using_expr) (ids : opt_identifier_list) : tactic . builtin

Definition intros (ids : opt_identifier_list) : tactic . builtin

Definition generalizes (es : expr_list) : tactic . builtin

Definition clears  (ids : identifier_list) : tactic . builtin

Definition reverts (ids : identifier_list) : tactic . builtin

Definition change (e : expr) : tactic . builtin

Definition assert_hypothesis (id : identifier) (e : expr) : tactic . builtin

Definition note_tac (id : identifier) (e : expr) : tactic . builtin

Definition constructor (k : option num)  : tactic . builtin
Definition fconstructor (k : option num) : tactic . builtin
Definition existsi (e : expr)            : tactic . builtin
Definition split                         : tactic . builtin
Definition left                          : tactic . builtin
Definition right                         : tactic . builtin

Definition injection (e : expr) (ids : opt_identifier_list) : tactic . builtin

Definition subst (ids : identifier_list) : tactic . builtin
Definition substvars : tactic . builtin

Definition reflexivity             : tactic . builtin
Definition symmetry                : tactic . builtin
Definition transitivity (e : expr) : tactic . builtin

Definition try         (t : tactic) : tactic . or_else t id
Definition repeat1     (t : tactic) : tactic . and_then t (repeat t)
Definition focus       (t : tactic) : tactic . focus_at t 0
Definition determ      (t : tactic) : tactic . at_most t 1
Definition trivial                  : tactic . or_else (apply eq.refl) assumption
Definition do (n : nat) (t : tactic) : tactic.
nat.rec id (fun n t' => and_then t t') n

Defined. tactic
tactic_infixl `;`:15 . tactic.and_then
tactic_notation T1 `:`:15 T2 . tactic.focus (tactic.and_then T1 (tactic.all_goals T2))
tactic_notation `(` h `|` r:(foldl `|` (e r, tactic.or_else r e) h) `)` . r
