Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "ThT     testt1t 1 The    iMNhq1TMNMNhqThehe" 43.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.