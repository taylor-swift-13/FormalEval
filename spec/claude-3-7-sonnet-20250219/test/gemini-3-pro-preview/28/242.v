Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long: concatenate_spec ["How"; "much"; "wood"; "aif"; "would"; "a"; "woodchuck"; "chuck"; "chukck"; "if"; "a"; "woodchuck"; "could"; "wood"; "chuck"] "Howmuchwoodaifwouldawoodchuckchuckchukckifawoodchuckcouldwoodchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.