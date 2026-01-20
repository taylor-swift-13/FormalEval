Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "hThT     testt1t 1 The    iMNhq1TMNMNhqThehe" 44.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.