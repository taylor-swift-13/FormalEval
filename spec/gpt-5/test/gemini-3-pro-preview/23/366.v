Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_vemThfGqorZJum5ymb0lsmtopsr : strlen_spec "vemThfGqorZJum5ymb0lsmtopsr" 27.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.