Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "  Tish!           4!n 

  1s  " 30.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.