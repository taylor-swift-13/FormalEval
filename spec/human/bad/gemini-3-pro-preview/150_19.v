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

(* Example proof for test case: input = [49; 0; 3], output = 3 *)
Example test_case : problem_150_spec 49 0 3 3.
Proof.
  unfold problem_150_spec.
  split.
  - intros H_prime.
    exfalso.
    destruct H_prime as [_ H_rel].
    specialize (H_rel 7).
    assert (1 <= 7 < 49)%Z as H_range by lia.
    specialize (H_rel H_range).
    unfold rel_prime in H_rel.
    vm_compute in H_rel.
    discriminate H_rel.
  - intros _.
    reflexivity.
Qed.