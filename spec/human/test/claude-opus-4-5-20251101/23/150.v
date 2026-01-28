Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_tabs : problem_23_spec "		" 2.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.