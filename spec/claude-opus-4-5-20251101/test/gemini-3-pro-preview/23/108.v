Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_sample : strlen_spec "This is a sample string to test the function" 44.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.