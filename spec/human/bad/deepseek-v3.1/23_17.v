Require Import String.
Require Import ZArith.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec (input : string) (output : nat) : Prop :=
  output = String.length input.

Example test_length_three_fourfive : problem_23_spec "three\nfour\nfive" 15.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.