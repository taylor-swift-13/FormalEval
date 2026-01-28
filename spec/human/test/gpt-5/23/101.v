Require Import String.
Require Import ZArith.
Require Import Ascii.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre ("one" ++ String (Ascii.ascii_of_nat 10) ("twot" ++ String (Ascii.ascii_of_nat 10) ("thrThis is a long string that has many characters in itee" ++ String (Ascii.ascii_of_nat 10) ("four" ++ String (Ascii.ascii_of_nat 10) "fiveabcdefghijklmnopqrstuvwxyz")))) ->
  exists output, problem_23_spec ("one" ++ String (Ascii.ascii_of_nat 10) ("twot" ++ String (Ascii.ascii_of_nat 10) ("thrThis is a long string that has many characters in itee" ++ String (Ascii.ascii_of_nat 10) ("four" ++ String (Ascii.ascii_of_nat 10) "fiveabcdefghijklmnopqrstuvwxyz")))) output /\ Z.of_nat output = 102%Z.
Proof.
  intros _.
  exists 102%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.