Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "thrieeThe quick brown f ox jumps over the lazy dogThe quick brown fox jumps overq the lazy dog
four
five " 105.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.