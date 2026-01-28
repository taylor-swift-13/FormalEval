Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["How"; "much"; "would"; "a"; "woodchuck"; "chuck"; "if"; "if"; "woodchuck"; "🐯🐯"; "could"; "chuck"; "wowoquvSickod"; "much"; "woodchuock"; "would"; "woodchuck"] "Howmuchwouldawoodchuckchuckififwoodchuck🐯🐯couldchuckwowoquvSickodmuchwoodchuockwouldwoodchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.