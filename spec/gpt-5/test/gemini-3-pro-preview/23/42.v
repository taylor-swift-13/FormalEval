Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "one
twot This striThis is a long streing that has many characters in itng has a 
 newline character
three
four
five" 115.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.