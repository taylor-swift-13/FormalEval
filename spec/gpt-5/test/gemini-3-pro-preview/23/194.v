Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_mThfGqorZJum5ymb0lsmtops : strlen_spec "mThfGqorZJum5ymb0lsmtops" 24.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.