Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_simple:
  concatenate_spec ["How"; "much"; "wood"; "would"; "if"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "coulld"; "chuck"; "wood"] "Howmuchwoodwouldifwoodchuckchuckifawoodchuckcoulldchuckwood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.