Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["How"; "much"; "wood"; "a"; "woodchuck"; "chuck"; "🧐"; "a"; "could"; "chuck"; "wood"] "Howmuchwoodawoodchuckchuck🧐acouldchuckwood".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.