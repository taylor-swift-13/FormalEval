Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Testing testingone
twot
thrThis is a long string that has many characters in itee
four
five 123" 95.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.