Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "   s is a sample    

 1s  string to te   " 42.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.