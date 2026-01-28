Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_Jum5ymb0lsmtops : strlen_spec "Jum5ymb0lsmtops" 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.