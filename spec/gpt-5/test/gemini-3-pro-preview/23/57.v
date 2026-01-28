Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Testing te stingone
twot
thrThis is a long string that has many characters in itee
four
five 123" 96.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.