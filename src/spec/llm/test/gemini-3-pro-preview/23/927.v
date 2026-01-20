Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_VhCV : strlen_spec "VhCV" 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.