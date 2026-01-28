Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "912345667890The quick brown fox jumps over the lazy This striThis is aaracter dogM" 82.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.