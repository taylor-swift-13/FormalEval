Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "GThT    1t 1 The    ic" 22.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.