Require Import String.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_123345 :
  problem_23_spec "123345" 6.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.