Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_nirs : strlen_spec "!nirs" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.