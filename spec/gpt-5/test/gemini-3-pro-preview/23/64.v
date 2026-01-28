Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "The quick brown fox jumps over the lazy This striThis is aaracter dogM" 70.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.