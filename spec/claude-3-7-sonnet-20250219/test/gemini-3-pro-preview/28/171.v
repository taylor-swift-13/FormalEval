Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_woodchuck: concatenate_spec ["How"; "much"; "wowod"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "could"] "Howmuchwowodwouldawoodchuckchuckifawoodchuckcouldchuckwoodcould".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.