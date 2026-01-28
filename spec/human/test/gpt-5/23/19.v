Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "The quick brown fox jumps over the lazy This striThis is a long string that has many characters in itng has a 
 newline character dog" ->
  exists output, problem_23_spec "The quick brown fox jumps over the lazy This striThis is a long string that has many characters in itng has a 
 newline character dog" output /\ Z.of_nat output = 133%Z.
Proof.
  intros _.
  exists 133%nat.
  split; [unfold problem_23_spec; vm_compute; reflexivity | simpl; reflexivity].
Qed.