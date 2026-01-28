Require Import String.
Open Scope string_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_case_1: problem_23_spec "The quick brzown fox jumps over the leazy Thisis is aaracter dog" 64.
Proof.
  unfold problem_23_spec.
  reflexivity.
Qed.