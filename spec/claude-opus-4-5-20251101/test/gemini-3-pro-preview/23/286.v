Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "why1N    This is a sampleto string to test the function          cJH1th" 71.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.