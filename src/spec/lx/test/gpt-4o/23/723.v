Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "    1tBrownsampBrownleLazy 1   " 31.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.