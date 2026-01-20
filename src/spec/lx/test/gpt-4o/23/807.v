Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DoMNhThis is a sample strintog to test the functiongmCV" 107.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.