Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_rrstr1ng : strlen_spec "rrstr1ng" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.