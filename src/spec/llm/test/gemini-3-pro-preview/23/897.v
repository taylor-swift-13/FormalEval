Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "w  CdV  1This is a sample sstrintogt ton test the functiont" 59.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.