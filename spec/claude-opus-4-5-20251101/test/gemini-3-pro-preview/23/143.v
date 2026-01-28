Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_utf8 : strlen_spec " ã          àèìòùáéíóúýâêîôûãñõäëïöüÿç" 65.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.