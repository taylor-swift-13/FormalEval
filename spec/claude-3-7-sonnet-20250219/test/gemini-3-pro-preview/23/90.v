Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "one
twotaa
thrThis is a long string that has many characters ien itee
1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5four
five" 175.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.