Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_p1sBrown :
  Spec "p1sBrown" 8.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.