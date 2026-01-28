Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "hThT     testt1t 1 The    iMNhq1TMNMNhqThehe" 44.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.