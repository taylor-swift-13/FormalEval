Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_rstn1r1n : strlen_spec "rstn1r1n" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.