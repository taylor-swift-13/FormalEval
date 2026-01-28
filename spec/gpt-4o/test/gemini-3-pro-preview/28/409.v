Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1 : concatenate_spec ["H🐼charactersw"; "How"; "much"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "a"; "wood"] "H🐼characterswHowmuchwouldawoodchuckchuckifawoodchuckcouldawood".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.