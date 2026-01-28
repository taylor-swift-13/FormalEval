Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_nonzero : strlen_spec "wwhyNcJH1thfunnchy1N" 20.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.