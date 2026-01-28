Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "one
twot This striThis is a long streing that has many characters in itng has a 
 newline character
three
four
five" ->
  exists output, problem_23_spec "one
twot This striThis is a long streing that has many characters in itng has a 
 newline character
three
four
five" output /\ Z.of_nat output = 115%Z.
Proof.
  intros _.
  exists 115%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.