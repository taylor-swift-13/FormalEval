Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_spaces : strlen_spec "i        s   " 13.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.