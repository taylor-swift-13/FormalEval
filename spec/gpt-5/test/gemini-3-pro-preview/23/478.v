Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_isJuis : strlen_spec "isJuis" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.