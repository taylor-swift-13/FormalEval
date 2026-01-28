Require Import Arith.
Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import List.
Require Import Lia.

(* 任意整数输入均可 *)
Definition problem_150_pre (n x y : Z) : Prop := True.

(*
  2. 程序 'x_or_y' 的规约
  参数:
    n : Z - 输入的整数，用于判断是否为素数。
    x : Z - 如果 n 是素数，则为预期输出。
    y : Z - 如果 n 不是素数，则为预期输出。
    res : Z - 程序的实际输出。

  规约逻辑:
  如果 prime n 为真，那么结果 res 必须等于 x；否则，结果 res 必须等于 y。
*)
Definition problem_150_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Example proof for test case: input = [-2; 0; 1], output = 1 *)
Example test_case : problem_150_spec (-2)%Z 0%Z 1%Z 1%Z.
Proof.
  unfold problem_150_spec.
  split.
  - intros H.
    destruct H as [Hlt _].
    lia.
  - intros _.
    reflexivity.
Qed.