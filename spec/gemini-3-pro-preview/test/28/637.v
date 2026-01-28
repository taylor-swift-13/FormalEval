Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_long : concatenate_spec ["woodch8789uck"; "How"; "wood"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "chuck"; "woodchuck"; "much"; "wood"] "woodch8789uckHowwoodwouldawoodchuckchuckifawoodchuckcouldchuckwoodchuckwoodchuckmuchwood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.