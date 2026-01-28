Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_long : strlen_spec "    This is a sample TTetnstrinisg tiiiso test the function           " 70.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.