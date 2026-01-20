Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "Th!s 1s 4 str1ng w1thTTBrownis    5ymb0ls !n 1t" 47.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.