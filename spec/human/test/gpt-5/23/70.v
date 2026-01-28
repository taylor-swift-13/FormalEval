Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "G1The quick brown f ox jumps over the lazy dog234  has a 
 newline character5NDKQyadEb" ->
  exists output, problem_23_spec "G1The quick brown f ox jumps over the lazy dog234  has a 
 newline character5NDKQyadEb" output /\ Z.of_nat output = 86%Z.
Proof.
  intros _.
  exists 86%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.