Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1 : concatenate_spec ["How"; "much"; "wood"; "would"; "thea"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "chuck"; "chuck"] "Howmuchwoodwouldtheaawoodchuckchuckifawoodchuckcouldchuckwoodchuckchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.