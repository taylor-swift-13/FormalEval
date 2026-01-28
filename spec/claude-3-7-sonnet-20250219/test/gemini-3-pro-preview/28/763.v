Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["How"; "much"; "wood"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "14"; "could"; "chuck"; "wood"; "chuck"; "a"] "Howmuchwoodwouldawoodchuckchuckifawoodchuck14couldchuckwoodchucka".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.