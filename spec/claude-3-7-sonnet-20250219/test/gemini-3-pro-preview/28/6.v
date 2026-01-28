Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_rps: concatenate_spec ["Rock"; "Paper"; "Scissors"] "RockPaperScissors".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.