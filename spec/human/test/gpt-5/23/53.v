Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "G1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree
four
fiveracter dogQyadEb" ->
  exists output, problem_23_spec "G1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree
four
fiveracter dogQyadEb" output /\ Z.of_nat output = 219%Z.
Proof.
  intros _.
  exists 219%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.