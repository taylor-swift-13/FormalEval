Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_Fox : strlen_spec "Fox" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.