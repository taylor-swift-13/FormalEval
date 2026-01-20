Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_GNDKQyadEb : strlen_spec "GNDKQyadEb" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.