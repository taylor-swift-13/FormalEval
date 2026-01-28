Require Import String.
Open Scope string_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_case_1: problem_23_spec "The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog" 69.
Proof.
  unfold problem_23_spec.
  reflexivity.
Qed.