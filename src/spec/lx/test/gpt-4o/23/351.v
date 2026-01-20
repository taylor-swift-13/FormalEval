Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "Ove    This is a sample    

 1s  string to test the functoion          r" 73.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.