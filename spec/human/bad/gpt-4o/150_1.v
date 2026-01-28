Require Import Arith.
Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.

Open Scope Z_scope.

(* 任意自然数输入均可 *)
Definition problem_150_pre (n x y : nat) : Prop := True.

(*
  规约逻辑:
  如果 prime (Z.of_nat n) 为真，那么结果 res 必须等于 x；否则，结果 res 必须等于 y。
*)
Definition problem_150_spec (n x y res : nat) : Prop :=
  (prime (Z.of_nat n) -> res = x) /\
  (~ prime (Z.of_nat n) -> res = y).

(* 辅助引理：7 是素数 *)
Lemma prime_7 : prime 7.
Proof.
  apply (prime_intro 7).
  - discriminate.
  - intros d Hd.
    destruct Hd as [H1 H2].
    assert (d = 1 \/ d = 7) by lia.
    destruct H; assumption.
Qed.

(* 辅助引理：15 不是素数 *)
Lemma not_prime_15 : ~ prime 15.
Proof.
  unfold prime. intros H.
  destruct (H 3).
  - lia.
  - exists 5. lia.
Qed.

(* x_or_y 函数实现 *)
Definition x_or_y (n x y : nat) : nat :=
  if prime_dec (Z.of_nat n) then x else y.

(* 测试用例的验证 *)
Example test_x_or_y_7_34_12 : problem_150_spec 7 34 12 34.
Proof.
  unfold problem_150_spec.
  split.
  - intros H. reflexivity.
  - intros H. exfalso. apply H. apply prime_7.
Qed.

(* 另一测试用例的验证 *)
Example test_x_or_y_15_8_5 : problem_150_spec 15 8 5 5.
Proof.
  unfold problem_150_spec.
  split.
  - intros H. exfalso. apply not_prime_15. apply H.
  - intros _. reflexivity.
Qed.