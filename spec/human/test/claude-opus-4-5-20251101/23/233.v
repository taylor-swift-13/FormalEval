Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_jum5ymb0lsmfunction : problem_23_spec "Jum5ymb0lsmfunction" 19.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.