Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long: concatenate_spec ["How"; "much"; "would"; "woodchuck"; "chuck"; "f"; "if"; "wook"; "could"; "chuck"; "wowoquvSickod"; "much"; "woodchuock"; "would"; "chuck"; "chuck"] "HowmuchwouldwoodchuckchuckfifwookcouldchuckwowoquvSickodmuchwoodchuockwouldchuckchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.