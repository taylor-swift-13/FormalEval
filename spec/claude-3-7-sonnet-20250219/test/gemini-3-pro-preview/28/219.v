Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["woood"; "How"; "much"; "wood"; "into"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "wood"; "much"] "wooodHowmuchwoodintowouldawoodchuckchuckifawoodchuckcouldchuckwoodwoodmuch".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.