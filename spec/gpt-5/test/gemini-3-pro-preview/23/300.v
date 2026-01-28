Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_non_empty : strlen_spec "!s40ls" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.