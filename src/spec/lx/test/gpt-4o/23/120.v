Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_spaces_and_1s :
  Spec "   

 1s  " 10.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.