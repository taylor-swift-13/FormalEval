Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "   
hy    This is a sample strinisg to test the fuunction          NcJH
  strin" 79.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.