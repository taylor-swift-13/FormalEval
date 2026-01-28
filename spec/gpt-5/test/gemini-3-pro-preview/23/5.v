Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_12345 : strlen_spec "12345" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.