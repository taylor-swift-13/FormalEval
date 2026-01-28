Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "This is a long string that has many characters in it" ->
  exists output, problem_23_spec "This is a long string that has many characters in it" output /\ Z.of_nat output = 52%Z.
Proof.
  intros _.
  exists 52%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.