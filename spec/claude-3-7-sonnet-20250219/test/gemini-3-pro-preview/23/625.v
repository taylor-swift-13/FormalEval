Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "ThT    1t 1 The    i" 20.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.