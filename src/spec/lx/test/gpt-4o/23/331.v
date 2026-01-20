Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_wtest5ymb0lse :
  Spec "wtest5ymb0lse" 13.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.