Require Import String.
Require Import Ascii.
Open Scope string_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_case_1: problem_23_spec (
  "Hello, WoG1234 This sitriThis is a long string that has many characters in itng has a " ++ String (ascii_of_nat 10) (
  " newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazby Thisthree" ++ String (ascii_of_nat 10) (
  "four" ++ String (ascii_of_nat 10) 
  "fiveracter dogQyadEborlod!"))) 235.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.