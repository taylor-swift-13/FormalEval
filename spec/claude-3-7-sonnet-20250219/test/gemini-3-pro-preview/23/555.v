Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_1 : strlen_spec "    This is a sample TTetnstrinisg tiiiso test the function       n    " 71.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.