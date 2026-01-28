Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec ["How"; "much"; "wood"; "couldthis
e
newlines"; "would"; "a"; "woodchuck"; "coculd"; "woodchuck"; "could"; "chuck"; "wood"; "much"; "woodchuck"] "Howmuchwoodcouldthis
e
newlineswouldawoodchuckcoculdwoodchuckcouldchuckwoodmuchwoodchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.