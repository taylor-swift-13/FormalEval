Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate : concatenate_spec ["How"; "ch🌞uck"; "much"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "much"; "would"; "would"] "Howch🌞uckmuchwouldawoodchuckchuckifawoodchuckcouldchuckwoodmuchwouldwould".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.