Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789" 99.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.