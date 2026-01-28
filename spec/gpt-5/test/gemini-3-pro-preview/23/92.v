Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen : strlen_spec "MThe quick brown fox jumps over the lazy This striThis is aaracter dogM" 71.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.