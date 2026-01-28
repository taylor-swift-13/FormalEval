Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_stricQukickn : strlen_spec "stricQukickn" 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.