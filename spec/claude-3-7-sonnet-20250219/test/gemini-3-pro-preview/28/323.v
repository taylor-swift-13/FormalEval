Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["This"; "mulntiple"; "How"; "much"; "wood"; "would"; "a"; "chuck"; "if"; "a"; "woodchuck"; "could"; "wood"; "How"] "ThismulntipleHowmuchwoodwouldachuckifawoodchuckcouldwoodHow".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.