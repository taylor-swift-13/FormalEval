Require Import Arith.
Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import List.
Require Import Lia.

(* 任意自然数输入均可 *)
Definition problem_150_pre (n x y : nat) : Prop := True.

(*
  2. 程序 'x_or_y' 的规约
  参数:
    n : nat - 输入的自然数，用于判断是否为素数。
    x : nat - 如果 n 是素数，则为预期输出。
    y : nat - 如果 n 不是素数，则为预期输出。
    res : nat - 程序的实际输出。

  规约逻辑:
  如果 prime (Z.of_nat n) 为真，那么结果 res 必须等于 x；否则，结果 res 必须等于 y。
*)
Definition problem_150_spec (n x y res : nat) : Prop :=
  (prime (Z.of_nat n) -> res = x) /\
  (~ prime (Z.of_nat n) -> res = y).

(* Example proof for test case: input = [62; 40; 20], output = 20 *)
Example test_case : problem_150_spec 62 40 20 20.
Proof.
  unfold problem_150_spec.
  split.
  - (* Case 1: prime (Z.of_nat 62) -> 20 = 40 *)
    intros H_prime.
    exfalso.
    simpl in H_prime.
    destruct H_prime as [_ H_rel].
    specialize (H_rel 2%Z).
    assert (H_range : (1 <= 2 < 62)%Z) by lia.
    apply H_rel in H_range.
    unfold rel_prime in H_range.
    vm_compute in H_range.
    discriminate H_range.
  - (* Case 2: ~ prime (Z.of_nat 62) -> 20 = 20 *)
    intros _.
    reflexivity.
Qed.