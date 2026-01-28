Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_woodchuck : concatenate_spec ["Ho"; "much"; "wood"; "would"; "a"; "woodchuck"; "chuck"; "wocodchuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "chuck"] "Homuchwoodwouldawoodchuckchuckwocodchuckifawoodchuckcouldchuckwoodchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.