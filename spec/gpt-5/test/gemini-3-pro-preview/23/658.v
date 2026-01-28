Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "     str1ng 1t  The    This is a sampleOvering to test the function" 67.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.