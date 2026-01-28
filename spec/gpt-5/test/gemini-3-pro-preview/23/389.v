Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "mThfGeeTeqorZJum5ymb0lsmtops" 28.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.