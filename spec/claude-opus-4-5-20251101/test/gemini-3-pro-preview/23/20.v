Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_1 : strlen_spec "1234 This striThis is a long string that has many characters in itng has a 
 newline character5" 95.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.