Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "Th1tBrownsampBrownleLazy!s 1s 4 str1str1ngng w1th 5ymb0ls !n 1tBrownLazys" 73.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.