Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "    4

  1s  " 13.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.