Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "MNMNhqThe CQuick Brown Fox JumpBrownL   
   azyses Over The BrownLazy DogmCV
hCV" 80.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.