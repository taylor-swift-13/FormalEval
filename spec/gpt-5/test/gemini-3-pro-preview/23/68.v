Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "one

twot
thrThis is a long string that has many characters in itee
foour
five" 78.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.