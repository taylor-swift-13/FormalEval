Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_unicode_string : strlen_spec "àèìòùáéíóúýâêîôûãñõäëïöüÿç" 52.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.