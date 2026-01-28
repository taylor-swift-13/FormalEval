Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["How"; "much"; "wowod"; "a"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "How"; "much"] "HowmuchwowodachuckifawoodchuckcouldchuckHowmuch".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.