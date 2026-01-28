Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_QuiisJumpsck : strlen_spec "QuiisJumpsck" 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.