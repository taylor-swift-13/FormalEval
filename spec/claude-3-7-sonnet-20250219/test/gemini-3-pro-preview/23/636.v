Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_sample : strlen_spec "This is a sample strintog ton test the function" 47.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.