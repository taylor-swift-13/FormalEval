Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_sentence: concatenate_spec ["How"; "much"; "wood"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "cotheauld"; "chuck"; "wood"; "chuck"] "Howmuchwoodwouldawoodchuckchuckifawoodchuckcotheauldchuckwoodchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.