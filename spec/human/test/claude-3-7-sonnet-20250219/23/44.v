Require Import String.
Require Import Coq.Strings.String.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_1223545 :
  problem_23_spec "1223545" 7.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.