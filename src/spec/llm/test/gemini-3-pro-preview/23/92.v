Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "MThe quick brown fox jumps over the lazy This striThis is aaracter dogM" 71.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.