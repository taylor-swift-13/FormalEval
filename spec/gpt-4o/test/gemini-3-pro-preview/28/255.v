Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_woodchuck : concatenate_spec ["How"; "much"; "wowod"; "a"; "woodchuck"; "chuck"; "iff"; "a"; "woodchuck"; "could"; "chuck"] "Howmuchwowodawoodchuckchuckiffawoodchuckcouldchuck".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.