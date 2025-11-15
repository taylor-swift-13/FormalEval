(* def fib(n: int):
Return n-th Fibonacci number.
>>> fib(10)
55
>>> fib(1)
1
>>> fib(8)
21
*)
(* 引入Coq标准库，用于自然数（nat）的定义 *)
Require Import Coq.Init.Nat.

(*
  is_fib 是一个逻辑关系，它用一阶逻辑的规则定义了斐波那契数列。
  它断言 "res 是第 n 个斐波那契数"。
  这是一个归纳定义 (Inductive) 的命题 (Prop)，由三个构造器（即公理）组成：

  - fib_zero: is_fib 0 0.
    这声明了“0 是第 0 个斐波那契数”为一个基本事实。

  - fib_one: is_fib 1 1.
    这声明了“1 是第 1 个斐波那契数”为另一个基本事实。

  - fib_step: forall n res_n res_n1,
                is_fib n res_n ->
                is_fib (S n) res_n1 ->
                is_fib (S (S n)) (res_n1 + res_n).
    这是一个逻辑蕴含规则：
    对于任意的 n, res_n, res_n1，
    如果（->）“res_n 是第 n 个斐波那契数” (is_fib n res_n)
    并且（->）“res_n1 是第 n+1 个斐波那契数” (is_fib (S n) res_n1)，
    那么我们可以推断出“res_n1 + res_n 是第 n+2 个斐波那契数” (is_fib (S (S n)) (res_n1 + res_n))。
    （在Coq中，S n 表示 n+1）
*)
Inductive is_fib : nat -> nat -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

(*
  fib_spec 是对 fib 函数的程序规约。

  参数：
  - n: nat    (代表程序的输入)
  - res: nat  (代表程序的输出)

*)
Definition fib_spec (n : nat) (res : nat) : Prop :=
  is_fib n res.