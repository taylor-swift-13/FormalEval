Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "w1th" ->
  exists output, problem_23_spec "w1th" output /\ Z.of_nat output = 4%Z.
Proof.
  intros _.
  exists 4%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.