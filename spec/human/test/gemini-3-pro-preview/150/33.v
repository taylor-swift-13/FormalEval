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

(* Example proof for test case: input = [49; 3; 3], output = 3 *)
Example test_case : problem_150_spec 49 3 3 3.
Proof.
  (* Unfold the specification definition *)
  unfold problem_150_spec.
  
  (* Split the conjunction into two implications *)
  split.
  
  - (* Case 1: prime (Z.of_nat 49) -> 3 = 3 *)
    intros _.
    reflexivity.
    
  - (* Case 2: ~ prime (Z.of_nat 49) -> 3 = 3 *)
    intros _.
    reflexivity.
Qed.