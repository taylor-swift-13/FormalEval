Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_sentence : strlen_spec "The quick brown f ox jumps over the lazy dog" 44.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.