Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "   
hy    This is a sample strinisg to test othe fuunction          NcJH
  string4" 82.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.