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

(* Test case:
input = [7%Z], output = 13%Z *)
Example problem_55_test_7 : problem_55_pre 7 /\ problem_55_spec 7 13.
Proof.
  split; [exact I|].
  pose proof fib_zero as H0.
  pose proof fib_one as H1.
  (* 2 -> 1 *)
  pose proof (fib_step 0 0 1 H0 H1) as H2.
  (* 3 -> 2 *)
  pose proof (fib_step 1 1 1 H1 H2) as H3.
  (* 4 -> 3 *)
  pose proof (fib_step 2 1 2 H2 H3) as H4.
  (* 5 -> 5 *)
  pose proof (fib_step 3 2 3 H3 H4) as H5.
  (* 6 -> 8 *)
  pose proof (fib_step 4 3 5 H4 H5) as H6.
  (* 7 -> 13 *)
  pose proof (fib_step 5 5 8 H5 H6) as H7.
  exact H7.
Qed.