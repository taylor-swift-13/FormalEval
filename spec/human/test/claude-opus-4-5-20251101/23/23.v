Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_11234567890 : problem_23_spec "11234567890" 11.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.