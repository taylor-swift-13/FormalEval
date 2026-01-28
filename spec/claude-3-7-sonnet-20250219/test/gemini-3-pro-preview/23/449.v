Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "LaàèìòùáéQFoxxukcky" 26.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.