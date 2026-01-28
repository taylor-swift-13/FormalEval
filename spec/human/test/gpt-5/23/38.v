Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "thrieeThe quick brown fox jumps overq the lazy dog
four
five" ->
  exists output, problem_23_spec "thrieeThe quick brown fox jumps overq the lazy dog
four
five" output /\ Z.of_nat output = 60%Z.
Proof.
  intros _.
  exists 60%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.