Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_wteb40ls : strlen_spec "wteb40ls" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.