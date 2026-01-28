Require Import String.
Open Scope string_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_case_1: problem_23_spec "1234 This sitriThis is a long string that has many character12345s in itng has a 
 newline character5" 101.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.