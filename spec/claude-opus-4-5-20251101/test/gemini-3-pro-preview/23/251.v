Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "   
hy    This is a sample strinisg to test the fuunction          NcJH
  string4" 81.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.