(*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
*)
prelude
import init.bool
open bool algebra

namespace pos_num
  protectedDefinition mul (a b : pos_num) : pos_num.
  pos_num.rec_on a
    b
    (fun n r => bit0 r + b)
    (fun n r => bit0 r)

Definition lt (a b : pos_num) : bool.
  pos_num.rec_on a
    (fun b => pos_num.cases_on b
      ff
      (fun m => tt)
      (fun m => tt))
    (fun n f b => pos_num.cases_on b
      ff
      (fun m => f m)
      (fun m => f m))
    (fun n f b => pos_num.cases_on b
      ff
      (fun m => f (succ m))
      (fun m => f m))
    b

Definition le (a b : pos_num) : bool.
  pos_num.lt a (succ b)
Defined. pos_num

Definition pos_num_has_mul [instance] : has_mul pos_num.
has_mul.mk pos_num.mul

namespace num
  open pos_num

Definition pred (a : num) : num.
  num.rec_on a zero (fun p => cond (is_one p) zero (pos (pred p)))

Definition size (a : num) : num.
  num.rec_on a (pos one) (fun p => pos (size p))

  protectedDefinition mul (a b : num) : num.
  num.rec_on a zero (fun pa => num.rec_on b zero (fun pb => pos (pos_num.mul pa pb)))
Defined. num

Definition num_has_mul [instance] : has_mul num.
has_mul.mk num.mul

namespace num
  protectedDefinition le (a b : num) : bool.
  num.rec_on a tt (fun pa => num.rec_on b ff (fun pb => pos_num.le pa pb))

  privateDefinition psub (a b : pos_num) : num.
  pos_num.rec_on a
    (fun b => zero)
    (fun n f b =>
      cond (pos_num.le (bit1 n) b)
        zero
        (pos_num.cases_on b
           (pos (bit0 n))
           (fun m => 2 * f m)
           (fun m => 2 * f m + 1)))
    (fun n f b =>
      cond (pos_num.le (bit0 n) b)
        zero
        (pos_num.cases_on b
           (pos (pos_num.pred (bit0 n)))
           (fun m => pred (2 * f m))
           (fun m => 2 * f m)))
    b

  protectedDefinition sub (a b : num) : num.
  num.rec_on a zero (fun pa => num.rec_on b a (fun pb => psub pa pb))
Defined. num

Definition num_has_sub [instance] : has_sub num.
has_sub.mk num.sub
