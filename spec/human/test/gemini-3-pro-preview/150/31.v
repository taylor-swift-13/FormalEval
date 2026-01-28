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

(* Example proof for test case: input = [37; 122; 455], output = 122 *)
Example test_case : problem_150_spec 37 122 455 122.
Proof.
  (* Unfold the specification definition *)
  unfold problem_150_spec.
  
  (* Split the conjunction into two implications *)
  split.
  
  - (* Case 1: prime (Z.of_nat 37) -> 122 = 122 *)
    intros _.
    reflexivity.
    
  - (* Case 2: ~ prime (Z.of_nat 37) -> 122 = 455 *)
    intros H_not_prime.
    exfalso. (* We derive False because 37 is actually prime *)
    apply H_not_prime.
    
    (* Prove that 37 is prime manually using the definition *)
    apply prime_intro.
    + (* Prove 1 < 37 *)
      simpl. lia.
    + (* Prove forall n, 1 <= n < 37 -> rel_prime n 37 *)
      intros n Hn.
      apply Zgcd_1_rel_prime.
      simpl in Hn.
      (* Since n is in [1, 37), we can enumerate all cases *)
      assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/ n = 31 \/ n = 32 \/ n = 33 \/ n = 34 \/ n = 35 \/ n = 36)%Z as H_cases by lia.
      repeat (destruct H_cases as [H_cases | H_cases]; [subst; vm_compute; reflexivity | ]).
      subst; vm_compute; reflexivity.
Qed.