Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_isJumps : strlen_spec "isJumps" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.