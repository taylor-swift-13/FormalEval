Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "Th!s 1s 4 str1ng w1th 5ymb0ls !n 1t" ->
  exists output, problem_23_spec "Th!s 1s 4 str1ng w1th 5ymb0ls !n 1t" output /\ Z.of_nat output = 35%Z.
Proof.
  intros _.
  exists 35%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.