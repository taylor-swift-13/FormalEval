Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "one
twot
thrThis is a long string thtat has many characters in itee
four
five" 77.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.