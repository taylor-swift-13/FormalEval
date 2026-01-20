Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "   

Bro   

 1s  n" 19.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.