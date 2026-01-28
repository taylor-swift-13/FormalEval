Require Import Coq.Init.Nat.
Require Import ZArith.
Require Import Lia.

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

(* Pre: no special constraints for `fib` *)
Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  is_fib n res.

(* Helper lemmas to build up the fibonacci sequence *)
Lemma is_fib_2 : is_fib 2 1.
Proof.
  replace 1 with (1 + 0) by lia.
  apply fib_step; [apply fib_zero | apply fib_one].
Qed.

Lemma is_fib_3 : is_fib 3 2.
Proof.
  replace 2 with (1 + 1) by lia.
  apply fib_step; [apply fib_one | apply is_fib_2].
Qed.

Example problem_55_test_1 : problem_55_spec 3 2.
Proof.
  unfold problem_55_spec.
  apply is_fib_3.
Qed.