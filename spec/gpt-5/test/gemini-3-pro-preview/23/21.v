Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "The quick brown fox jumps over the lazy This striThis is aaracter dog" 69.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.