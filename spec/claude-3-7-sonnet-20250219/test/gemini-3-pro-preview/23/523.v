Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "striing     This is a sampl          tothe func tion          " 62.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.