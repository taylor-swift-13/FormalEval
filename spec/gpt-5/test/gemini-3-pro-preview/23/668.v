Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "     str1ng 1t  The    This is a samp leOvering to test the function" 68.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.