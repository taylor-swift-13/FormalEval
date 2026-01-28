Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_vemThfGqorZJum5ymb0lsmtopsr : strlen_spec "vemThfGqorZJum5ymb0lsmtopsr" 27.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.