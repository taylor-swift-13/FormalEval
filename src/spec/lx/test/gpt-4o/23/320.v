Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "RL   

  1s  kion" 17.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.