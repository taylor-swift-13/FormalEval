Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_FMc : strlen_spec "FMc" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.