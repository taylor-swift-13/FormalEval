Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_woodchuck: concatenate_spec ["How"; "much"; "would"; "if"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "coulld"; "chuck"; "wood"; "chuck"; "much"] "Howmuchwouldifwoodchuckchuckifawoodchuckcoulldchuckwoodchuckmuch".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.