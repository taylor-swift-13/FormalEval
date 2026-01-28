Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_w1thTTBrownis : strlen_spec "w1thTTBrownis" 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.