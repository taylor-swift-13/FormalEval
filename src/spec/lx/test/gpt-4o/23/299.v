Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "   
hy    This is a sample strinisg to test othe fuunction          NcJH
  string4" 82.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.