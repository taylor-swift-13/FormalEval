Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_sample : strlen_spec "    This is a sample strintg to test the function          " 59.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.