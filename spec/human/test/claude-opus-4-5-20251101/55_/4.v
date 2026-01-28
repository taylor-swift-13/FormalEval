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

Lemma is_fib_4 : is_fib 4 3.
Proof.
  replace 3 with (2 + 1) by lia.
  apply fib_step; [apply is_fib_2 | apply is_fib_3].
Qed.

Lemma is_fib_5 : is_fib 5 5.
Proof.
  replace 5 with (3 + 2) by lia.
  apply fib_step; [apply is_fib_3 | apply is_fib_4].
Qed.

Lemma is_fib_6 : is_fib 6 8.
Proof.
  replace 8 with (5 + 3) by lia.
  apply fib_step; [apply is_fib_4 | apply is_fib_5].
Qed.

Lemma is_fib_7 : is_fib 7 13.
Proof.
  replace 13 with (8 + 5) by lia.
  apply fib_step; [apply is_fib_5 | apply is_fib_6].
Qed.

Lemma is_fib_8 : is_fib 8 21.
Proof.
  replace 21 with (13 + 8) by lia.
  apply fib_step; [apply is_fib_6 | apply is_fib_7].
Qed.

Lemma is_fib_9 : is_fib 9 34.
Proof.
  replace 34 with (21 + 13) by lia.
  apply fib_step; [apply is_fib_7 | apply is_fib_8].
Qed.

Lemma is_fib_10 : is_fib 10 55.
Proof.
  replace 55 with (34 + 21) by lia.
  apply fib_step; [apply is_fib_8 | apply is_fib_9].
Qed.

Lemma is_fib_11 : is_fib 11 89.
Proof.
  replace 89 with (55 + 34) by lia.
  apply fib_step; [apply is_fib_9 | apply is_fib_10].
Qed.

Example problem_55_test_1 : problem_55_spec 11 89.
Proof.
  unfold problem_55_spec.
  apply is_fib_11.
Qed.