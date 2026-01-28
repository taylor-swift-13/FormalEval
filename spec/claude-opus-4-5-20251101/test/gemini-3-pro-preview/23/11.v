Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_example : strlen_spec "one
two
three
four
five" 23.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.