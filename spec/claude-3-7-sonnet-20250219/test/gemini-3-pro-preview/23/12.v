Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_digits : strlen_spec "1234567890" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.