Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "  Tish!           4!n 

  1s  " 30.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.