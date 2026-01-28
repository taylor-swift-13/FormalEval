Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_long : strlen_spec "This is a sample string    This is a sampl            eto string to test the func Theon           to test the function" 118.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.