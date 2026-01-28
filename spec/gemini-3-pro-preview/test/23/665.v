Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_long : strlen_spec "BBrownLMNhqThe CQuick BrMNhqThe Quick Brown Fox Jumps Over The BrownLazy DogmCVown Fox Jumpes Over The BrownLazy DogmCVaazyLazy  " 129.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.