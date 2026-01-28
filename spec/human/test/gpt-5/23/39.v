Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "one
twot
three
four
fiv" ->
  exists output, problem_23_spec "one
twot
three
four
fiv" output /\ Z.of_nat output = 23%Z.
Proof.
  intros _.
  exists 23%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.