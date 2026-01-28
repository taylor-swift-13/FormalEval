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

(* Example proof for test case: input = [17; 5; 9], output = 5 *)
Example test_case : problem_150_spec 17 5 9 5.
Proof.
  (* Unfold the specification definition *)
  unfold problem_150_spec.
  
  (* Split the conjunction into two implications *)
  split.
  
  - (* Case 1: prime (Z.of_nat 17) -> 5 = 5 *)
    intros _.
    reflexivity.
    
  - (* Case 2: ~ prime (Z.of_nat 17) -> 5 = 9 *)
    intros H_not_prime.
    exfalso. (* We derive False because 17 is actually prime *)
    apply H_not_prime.
    
    (* Prove that 17 is prime manually using the definition *)
    apply prime_intro.
    + (* Prove 1 < 17 *)
      simpl. lia.
    + (* Prove forall n, 1 <= n < 17 -> rel_prime n 17 *)
      intros n Hn.
      apply Zgcd_1_rel_prime.
      simpl in Hn.
      (* Since n is in [1, 17), we can enumerate all cases *)
      assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ 
              n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16)%Z as H_cases by lia.
      repeat (destruct H_cases as [? | H_cases]; [subst; vm_compute; reflexivity | ]).
      subst; vm_compute; reflexivity.
Qed.