Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_mThfGqorZJum5ymb0lsmtops : strlen_spec "mThfGqorZJum5ymb0lsmtops" 24.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.