Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "one
twota
thrThis is a long string that has many characters ien itee
four
five" 78.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.