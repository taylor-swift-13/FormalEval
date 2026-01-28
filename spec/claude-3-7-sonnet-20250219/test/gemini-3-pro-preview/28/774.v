Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_woodchuck: concatenate_spec ["How"; "much"; "wood"; "wouisld"; "if"; "woodchuck"; "chuck"; "if"; "couldd"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "woodchuck"] "Howmuchwoodwouisldifwoodchuckchuckifcoulddawoodchuckcouldchuckwoodwoodchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.