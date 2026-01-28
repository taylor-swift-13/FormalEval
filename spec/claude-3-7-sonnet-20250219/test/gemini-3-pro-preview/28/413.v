Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["How"; "much"; "would"; "a"; "chuck"; "a"; "aa"; "woodchuck"; "could"; "wood"] "Howmuchwouldachuckaaawoodchuckcouldwood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.