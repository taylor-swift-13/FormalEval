Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_newline :
  Spec "GNDThis string has a 
 newline characterdEb" 43.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.