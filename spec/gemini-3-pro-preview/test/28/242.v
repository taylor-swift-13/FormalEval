Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_woodchuck : concatenate_spec ["How"; "much"; "wood"; "aif"; "would"; "a"; "woodchuck"; "chuck"; "chukck"; "if"; "a"; "woodchuck"; "could"; "wood"; "chuck"] "Howmuchwoodaifwouldawoodchuckchuckchukckifawoodchuckcouldwoodchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.