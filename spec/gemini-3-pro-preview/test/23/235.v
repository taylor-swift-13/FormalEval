Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_spaces : strlen_spec "        funthec    " 19.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.