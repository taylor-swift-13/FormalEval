Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_912345667890 : problem_23_spec "912345667890" 12.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.