Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_woodchuck: concatenate_spec ["How"; "much"; "would"; "a"; "woodchuck"; "chuck"; "if"; "if"; "woodchuck"; "could"; "chuck"; "wowoquvSickod"; "much"; "woodchuock"; "would"] "HowmuchwouldawoodchuckchuckififwoodchuckcouldchuckwowoquvSickodmuchwoodchuockwould".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.