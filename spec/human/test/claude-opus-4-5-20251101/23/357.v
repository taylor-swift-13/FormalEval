Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_pFomThfGqorZJum5ymb0lsmtopss : problem_23_spec "pFomThfGqorZJum5ymb0lsmtopss" 28.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.