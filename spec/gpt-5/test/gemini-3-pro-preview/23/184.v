Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen : strlen_spec "Jum5ymb0lsmtops" 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.