Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "one
twota
thrThis is a long string that has many chone
twot
thrThis is a long string that has  many characters in itee
four
fivearacters in itee
four
five" ->
  exists output, problem_23_spec "one
twota
thrThis is a long string that has many chone
twot
thrThis is a long string that has  many characters in itee
four
fivearacters in itee
four
five" output /\ Z.of_nat output = 154%Z.
Proof.
  intros _.
  exists 154%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.