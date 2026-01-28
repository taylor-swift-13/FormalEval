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

(* Example proof for test case: input = [6; 34; 1234], output = 1234 *)
Example test_case : problem_150_spec 6 34 1234 1234.
Proof.
  unfold problem_150_spec.
  split.
  - (* Case 1: prime 6 -> 1234 = 34 *)
    intros H_prime.
    exfalso.
    (* Prove 6 is not prime because 2 divides 6 *)
    assert (H_div : (2 | Z.of_nat 6)%Z).
    { exists 3%Z. reflexivity. }
    pose proof (prime_divisors _ H_prime _ H_div) as H_contra.
    lia.
  - (* Case 2: ~ prime 6 -> 1234 = 1234 *)
    intros _.
    reflexivity.
Qed.