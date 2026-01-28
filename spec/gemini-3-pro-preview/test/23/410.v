Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "    This is a sampl           eto string to test thes func tion          " 73.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.