Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_LqNCZA : strlen_spec "LqNCZA" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.