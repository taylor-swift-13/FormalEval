Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "   

wtest5ymb40ls    " 22.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.