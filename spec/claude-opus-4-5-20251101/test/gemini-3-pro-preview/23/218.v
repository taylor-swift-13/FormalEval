Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "funtThis is a sample string    This is a sampl            eto string to test the func Theon           to test the functionhec" 125.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.