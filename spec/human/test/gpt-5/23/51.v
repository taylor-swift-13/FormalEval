Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "G1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKQyadEb" ->
  exists output, problem_23_spec "G1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKQyadEb" output /\ Z.of_nat output = 106%Z.
Proof.
  intros _.
  exists 106%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.