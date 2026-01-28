Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["How"; "much"; "wood"; "couldthis
e
newlines"; "would"; "a"; "woodchuck"; "a"; "coculd"; "woodchuck"; "could"; "chuck"; "wood"; "much"] "Howmuchwoodcouldthis
e
newlineswouldawoodchuckacoculdwoodchuckcouldchuckwoodmuch".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.