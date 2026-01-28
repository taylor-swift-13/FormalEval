Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_case1 : strlen_spec "one
twota
thrThis is a long string that has many characters in itee
four
five" 77.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.