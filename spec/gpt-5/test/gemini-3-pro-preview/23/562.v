Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_spaces : strlen_spec "    This is a           " 24.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.