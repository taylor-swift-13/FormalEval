Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "
zTTBrownismbUmvrKpesBrMNhqThe
Th!s 1s 4 str1str1ngng w1th 5ymb0lDogmVCVBBrownLazyLazy  s !n 1tBrow
" 100.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.