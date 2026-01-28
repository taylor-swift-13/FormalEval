Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_RLkion : problem_23_spec "RLkion" 6.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.