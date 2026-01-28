Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_newline : strlen_spec "1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5" 96.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.