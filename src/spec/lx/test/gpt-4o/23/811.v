Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "MNhqThe CQuick Brown Fox Jumpes OveJr The BrownLazy DogmBrownCV" 63.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.