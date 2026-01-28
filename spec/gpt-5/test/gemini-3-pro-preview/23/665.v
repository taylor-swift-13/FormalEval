Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "BBrownLMNhqThe CQuick BrMNhqThe Quick Brown Fox Jumps Over The BrownLazy DogmCVown Fox Jumpes Over The BrownLazy DogmCVaazyLazy  " 129.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.