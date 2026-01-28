Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_input : strlen_spec "1234 This striThis is a long string that has many characters in itng has a 
 newline character5" 95.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.