Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_custom : strlen_spec "    This is a sample strinisg to test the functiostgrsr1ngLqNCZAtestn          " 79.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.