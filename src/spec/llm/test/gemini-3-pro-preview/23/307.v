Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "       This is a sample string to test the function          1s  " 65.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.