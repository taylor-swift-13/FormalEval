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

(* Example proof for test case: input = [31; -5; 22], output = -5 *)
Example test_case : problem_150_spec 31 (-5) 22 (-5).
Proof.
  (* Unfold the specification definition *)
  unfold problem_150_spec.
  
  (* Split the conjunction into two implications *)
  split.
  
  - (* Case 1: prime 31 -> -5 = -5 *)
    intros _.
    reflexivity.
    
  - (* Case 2: ~ prime 31 -> -5 = 22 *)
    intros H_not_prime.
    exfalso. (* We derive False because 31 is actually prime *)
    apply H_not_prime.
    
    (* Prove that 31 is prime manually using the definition *)
    apply prime_intro.
    + (* Prove 1 < 31 *)
      simpl. lia.
    + (* Prove forall n, 1 <= n < 31 -> rel_prime n 31 *)
      intros n Hn.
      apply Zgcd_1_rel_prime.
      simpl in Hn.
      (* Since n is in [1, 31), we can enumerate all cases *)
      assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
              n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/
              n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30)%Z as H_cases by lia.
      repeat match goal with
             | [ H : _ \/ _ |- _ ] => destruct H as [? | ?]
             end; subst; vm_compute; reflexivity.
Qed.