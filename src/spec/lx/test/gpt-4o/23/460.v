Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_example :
  Spec "     o test the function1s  " 28.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.