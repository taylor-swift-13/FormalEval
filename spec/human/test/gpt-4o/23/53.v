Require Import String.
Require Import Ascii.
Require Import List.
Import ListNotations.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec (input : string) (output : nat) : Prop :=
  output = length (string_to_list input).

Example problem_23_test_case_1 :
  problem_23_spec "G1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree
four
fiveracter dogQyadEb" 219.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.