Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_wood : concatenate_spec ["How"; "much"; "wood"; "would"; "a"; "chuck"; "if"; "a"; "aa"; "woodchuck"; "could"; "wood"] "Howmuchwoodwouldachuckifaaawoodchuckcouldwood".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.