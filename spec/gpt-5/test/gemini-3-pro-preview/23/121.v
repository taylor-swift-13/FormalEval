Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_jumps : strlen_spec "Jumps" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.