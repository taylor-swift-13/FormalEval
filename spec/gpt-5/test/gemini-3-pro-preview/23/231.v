Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen : strlen_spec "The QuiisJumpsck Brown Fox Jg" 29.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.