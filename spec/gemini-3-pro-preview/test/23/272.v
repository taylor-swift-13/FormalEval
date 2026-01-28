Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_fux : strlen_spec "fux" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.