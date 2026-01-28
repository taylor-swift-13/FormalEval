Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "Tish!          This is a sample string    This is a sampl   unction!n4" 70.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.