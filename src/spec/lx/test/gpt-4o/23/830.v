Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "This i s a sample strintog to test the hfuncti on" 49.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.