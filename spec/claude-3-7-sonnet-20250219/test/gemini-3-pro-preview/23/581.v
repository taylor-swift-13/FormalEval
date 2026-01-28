Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_long : strlen_spec "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789" 99.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.