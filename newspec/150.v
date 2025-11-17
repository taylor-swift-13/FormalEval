(* def x_or_y(n, x, y):
"""A simple program which should return the value of x if n is
a prime number and should return the value of y otherwise.

Examples:
for x_or_y(7, 34, 12) == 34
for x_or_y(15, 8, 5) == 5

""" *)
(* 导入Coq算术库，以使用取模运算(mod)和大小比较 *)
Require Import Arith.

(* 任意自然数输入均可 *)
Definition Pre (n x y : nat) : Prop := True.

(*
  1. 自定义 'MyPrime' (素数) 规约，使用取模运算
  这个定义更加接近于一个可执行的素数判断逻辑。

  一个自然数 n 是素数，当且仅当:
  - n > 1
  - 并且，对于所有大于等于2且小于n的自然数d，n mod d 的结果都不为0。
*)
Definition Prime (n : nat) : Prop :=
  (1 < n) /\ (forall d : nat, 2 <= d -> d < n -> n mod d <> 0).

(*
  2. 程序 'x_or_y' 的规约
  参数:
    n : nat - 输入的自然数，用于判断是否为素数。
    x : nat - 如果 n 是素数，则为预期输出。
    y : nat - 如果 n 不是素数，则为预期输出。
    res : nat - 程序的实际输出。

  规约逻辑:
  如果 MyPrime n 为真，那么结果 res 必须等于 x；否则，结果 res 必须等于 y。
*)
Definition x_or_y_spec (n x y res : nat) : Prop :=
  Prime n -> res = x \/
  ~ Prime n -> res = y.