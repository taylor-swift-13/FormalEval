Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_sample : strlen_spec "    This is a sample TTetnstrinisg to test the function           " 66.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.