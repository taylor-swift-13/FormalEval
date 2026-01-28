Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_long : strlen_spec "    This is a sample strinisg to test the functiostgrsr1ngLqNCZAtestn          " 79.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.