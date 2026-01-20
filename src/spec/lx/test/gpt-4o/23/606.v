Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "MNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCV
" 58.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.