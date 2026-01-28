Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_r1ng : strlen_spec "r1ng" 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.