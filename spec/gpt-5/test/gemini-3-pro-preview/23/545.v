Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_yyy : strlen_spec "yyy" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.