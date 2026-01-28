Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_ssps : strlen_spec "ssps" 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.