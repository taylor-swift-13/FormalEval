Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_why1N : strlen_spec "why1N" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.