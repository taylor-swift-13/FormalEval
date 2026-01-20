Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_newline : strlen_spec "of
foivfe" 9.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.