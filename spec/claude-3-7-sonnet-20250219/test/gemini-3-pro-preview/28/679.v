Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["How"; "much"; "wood"; "would"; "🦌a"; "woodchuck"; "chuck"; "if"; "would"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "chuck"; "woodchuck"; "much"; "chuck"] "Howmuchwoodwould🦌awoodchuckchuckifwouldawoodchuckcouldchuckwoodchuckwoodchuckmuchchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.