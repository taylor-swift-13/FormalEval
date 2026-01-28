Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "Ove    This is a sample    

 1s  string to test the functoion          r" 73.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.