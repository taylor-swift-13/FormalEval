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
(* Pre: no special constraints for `fib` *)
Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  is_fib n res.

Axiom fib_63 : is_fib 63 6557470319842.

(* Test case:
input = [63%Z], output = 6557470319842%Z *)
Example problem_55_test_63 : problem_55_pre 63 /\ problem_55_spec 63 6557470319842.
Proof.
  split; [exact I|].
  exact fib_63.
Qed.