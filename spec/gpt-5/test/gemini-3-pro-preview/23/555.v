Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "    This is a sample TTetnstrinisg tiiiso test the function       n    " 71.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.