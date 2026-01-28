Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_woodchuck : concatenate_spec ["How"; "much"; "wood"; "would"; "🦌a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "chuck"; "odchuck"; "much"; "chuck"] "Howmuchwoodwould🦌awoodchuckchuckifawoodchuckcouldchuckwoodchuckodchuckmuchchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.