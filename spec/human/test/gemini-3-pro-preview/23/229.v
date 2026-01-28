Require Import String.
Open Scope string_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_case_1: problem_23_spec "Th!s40ls !n 1t   

 wwtest5ymb40ls    
" 39.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.