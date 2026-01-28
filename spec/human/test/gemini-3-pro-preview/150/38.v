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

(* Example proof for test case: input = [36; 456; 37], output = 37 *)
Example test_case : problem_150_spec 36 456 37 37.
Proof.
  unfold problem_150_spec.
  split.
  - intros H_prime.
    exfalso.
    assert (H_div: (2 | Z.of_nat 36)%Z).
    { exists 18%Z. reflexivity. }
    apply prime_divisors with (a := 2%Z) in H_prime; try assumption.
    simpl in H_prime. lia.
  - intros _.
    reflexivity.
Qed.