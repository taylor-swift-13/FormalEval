Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "striing     This is a sampl          tothe func tion          " 62.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.