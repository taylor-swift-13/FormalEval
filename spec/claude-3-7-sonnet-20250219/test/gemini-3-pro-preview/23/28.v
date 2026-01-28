Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_long : strlen_spec "one
twot
thrThis is a long string thtat has many characters in itee
four
five" 77.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.