Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "Testing testingone
twot
thrThis is a long string that has many characters in itee
four
five 123" 95.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.