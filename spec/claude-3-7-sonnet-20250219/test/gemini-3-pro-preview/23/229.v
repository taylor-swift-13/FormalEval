Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "Th!s40ls !n 1t   

 wwtest5ymb40ls    
" 39.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.