Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_newline :
  Spec "This string has a \n newline character" 38.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.