Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_1 : strlen_spec "1234 This sitriThis is a long string that has many character12345s in itng has a 
 newline character5" 101.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.