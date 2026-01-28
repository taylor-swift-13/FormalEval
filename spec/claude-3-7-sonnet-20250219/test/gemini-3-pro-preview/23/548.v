Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "Juom5This is a sample string    This is a sampl            eto string to test the func Theon       to test the functionymbops" 125.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.