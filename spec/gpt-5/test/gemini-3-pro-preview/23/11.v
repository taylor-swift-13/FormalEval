Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_multiline : strlen_spec "one
two
three
four
five" 23.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.