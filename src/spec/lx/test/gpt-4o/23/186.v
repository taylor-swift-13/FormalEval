Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_spaces_and_characters :
  Spec "   

  1s  " 11.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.