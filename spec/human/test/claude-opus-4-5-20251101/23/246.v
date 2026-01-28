Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_long : problem_23_spec "This is a sample string    This is a sampl            eto string to test the func Theon       to test the function" 114.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.