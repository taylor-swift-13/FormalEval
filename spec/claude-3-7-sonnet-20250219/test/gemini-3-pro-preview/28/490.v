Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["How"; "much"; "wood"; "couldthis\ne\nnewlines"; "would"; "a"; "woodchuck"; "coculd"; "woodchuck"; "could"; "chuck"; "wood"; "much"; "woodchuck"] "Howmuchwoodcouldthis\ne\nnewlineswouldawoodchuckcoculdwoodchuckcouldchuckwoodmuchwoodchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.