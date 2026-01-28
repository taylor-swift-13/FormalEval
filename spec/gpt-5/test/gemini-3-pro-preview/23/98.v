Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "The quick brown fox11234567890 jumps over the lazy This striThis is aaracter dog" 80.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.