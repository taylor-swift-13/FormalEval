Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_symbols :
  Spec "s    

 !fu55ymb0lsnc!ntion  e" 30.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.