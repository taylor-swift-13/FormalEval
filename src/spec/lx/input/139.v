(* def special_factorial(n):
"""The Brazilian factorial is defined as:
brazilian_factorial(n) = n! * (n-1)! * (n-2)! * ... * 1!
where n > 0

For example:
>>> special_factorial(4)
288

The function will receive an integer as input and should return the special
factorial of this integer.
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

(* 简单定义阶乘（用于 Spec，非证明） *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => n * fact k
  end.

(* special_factorial(n) := ∏_{i = 1..n} i! （当 n = 0 时按约定为 1） *)
Definition brazilian_factorial_value (n : nat) : nat :=
  fold_right mult 1 (map fact (seq 1 n)).

(* Spec：r 恰好等于从 1 到 n 的阶乘的乘积 *)
Definition special_factorial_spec (n : nat) (r : nat) : Prop :=
  r = brazilian_factorial_value n.
