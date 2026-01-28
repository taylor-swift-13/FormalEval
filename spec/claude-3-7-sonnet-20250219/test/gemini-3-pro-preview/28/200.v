Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_phrase: concatenate_spec ["How"; "much"; "wowod"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "🐯"; "wood"] "Howmuchwowodwouldawoodchuckchuckifawoodchuckcouldchuck🐯wood".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.