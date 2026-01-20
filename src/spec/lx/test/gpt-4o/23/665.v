Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_large :
  Spec "BBrownLMNhqThe CQuick BrMNhqThe Quick Brown Fox Jumps Over The BrownLazy DogmCVown Fox Jumpes Over The BrownLazy DogmCVaazyLazy  " 129.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.