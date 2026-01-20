Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789" 99.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.