Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_quick_brown_fox : problem_23_spec "The quick brown fox jumps over the lazy dog" 43.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.