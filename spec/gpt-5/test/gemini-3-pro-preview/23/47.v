Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5" 96.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.