Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_wteb40ls :
  Spec "wteb40ls" 8.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.