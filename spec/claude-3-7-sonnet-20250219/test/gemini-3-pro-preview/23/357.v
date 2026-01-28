Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_pFomThfGqorZJum5ymb0lsmtopss : strlen_spec "pFomThfGqorZJum5ymb0lsmtopss" 28.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.