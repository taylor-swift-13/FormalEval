Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "   
hy    This is a sample strinisg to ttest the fuunction          NcJH
  string" 81.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.