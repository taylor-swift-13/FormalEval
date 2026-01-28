Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_wood: concatenate_spec ["How"; "much"; "wood"; "a"; "woodchuck"; "chuck"; "if"; "a"; "could"; "chuck"; "wood"] "Howmuchwoodawoodchuckchuckifacouldchuckwood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.