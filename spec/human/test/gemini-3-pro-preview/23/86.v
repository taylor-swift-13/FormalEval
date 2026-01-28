Require Import String.
Require Import Ascii.
Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_case_1: problem_23_spec ("one" ++ String (ascii_of_nat 10) "twota" ++ String (ascii_of_nat 10) "thrThis is a long string that has many characters ien itee" ++ String (ascii_of_nat 10) "four" ++ String (ascii_of_nat 10) "five") 78.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.