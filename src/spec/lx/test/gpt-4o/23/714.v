Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "ThT     testt1t 1 The    iMNhq1TMNMNhqThehe" 43.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.