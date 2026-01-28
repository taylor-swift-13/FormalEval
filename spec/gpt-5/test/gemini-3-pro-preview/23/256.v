Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_sentence : strlen_spec "The Quick Brown Fox Jumpe Lazy Dog" 34.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.