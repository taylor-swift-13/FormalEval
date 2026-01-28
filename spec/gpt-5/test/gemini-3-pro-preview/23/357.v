Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_pFomThfGqorZJum5ymb0lsmtopss : strlen_spec "pFomThfGqorZJum5ymb0lsmtopss" 28.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.