Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_Jum5ymb0lsmfunction : strlen_spec "Jum5ymb0lsmfunction" 19.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.