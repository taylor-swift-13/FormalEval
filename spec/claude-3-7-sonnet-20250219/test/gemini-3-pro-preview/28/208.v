Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_phrase: concatenate_spec ["How"; "much"; "wood"; "a"; "woodchuck"; "if"; "a"; "could"; "chuck"; "wood"] "Howmuchwoodawoodchuckifacouldchuckwood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.