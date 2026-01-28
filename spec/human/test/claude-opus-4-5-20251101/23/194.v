Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_mThfGqorZJum5ymb0lsmtops : problem_23_spec "mThfGqorZJum5ymb0lsmtops" 24.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.