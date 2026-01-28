Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long: concatenate_spec ["How"; "much"; "wood"; "would"; "a"; "chuck"; "if"; "a"; "aa"; "woodchuck"; "could"; "wood"; "How"] "HowmuchwoodwouldachuckifaaawoodchuckcouldwoodHow".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.