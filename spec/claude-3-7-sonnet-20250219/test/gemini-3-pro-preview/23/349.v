Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_fuon : strlen_spec "fuon" 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.