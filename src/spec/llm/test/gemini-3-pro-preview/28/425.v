Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_1 : concatenate_spec ["How"; "much"; "would"; "woodchuck"; "chuck"; "f"; "if"; "wook"; "could"; "chuck"; "wowoquvSickod"; "much"; "woodchuock"; "would"; "chuck"; "chuck"] "HowmuchwouldwoodchuckchuckfifwookcouldchuckwowoquvSickodmuchwoodchuockwouldchuckchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.