Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "   
hy    This is a sample strinisg to test the fuunction          NcJH
  string" 80.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.