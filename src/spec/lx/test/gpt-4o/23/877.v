Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_CQuicJumpskg :
  Spec "CQuicJumpskg" 12.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.