Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "one
twota
thrThis is a long string that has many characters iThe quick bis striThis is aaracter dogMen itee
four
five" 117.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.