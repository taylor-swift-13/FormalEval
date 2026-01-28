Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec 
  ["How"; "much"; "would"; "a"; "woodchuck"; "chuck"; "if"; "if"; "woodchuck"; "🐯🐯"; "could"; "chuck"; "wowoquvSickod"; "much"; "woodchuock"; "would"; "woodchuck"]
  "Howmuchwouldawoodchuckchuckififwoodchuck🐯🐯couldchuckwowoquvSickodmuchwoodchuockwouldwoodchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.