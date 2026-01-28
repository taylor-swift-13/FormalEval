Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_sample : strlen_spec "Tish!          This is a sample string    This is a sampl   unction4" 68.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.