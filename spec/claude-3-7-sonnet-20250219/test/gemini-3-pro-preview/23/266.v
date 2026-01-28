Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_wtest5ymb40ls : strlen_spec "wtest5ymb40ls" 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.