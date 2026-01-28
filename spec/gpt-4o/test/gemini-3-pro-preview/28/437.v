Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate : concatenate_spec ["How"; "much"; "wood"; "would"; "a"; "woodchuck"; "chuck"; "a"; "coculd"; "woodchuck"; "could"; "chuck"; "wood"; "much"] "Howmuchwoodwouldawoodchuckchuckacoculdwoodchuckcouldchuckwoodmuch".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.