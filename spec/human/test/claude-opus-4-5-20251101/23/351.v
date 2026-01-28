Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_sample : problem_23_spec "Ove    This is a sample    

 1s  string to test the functoion          r" 73.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.