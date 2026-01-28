Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_ps : strlen_spec "ps" 2.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.