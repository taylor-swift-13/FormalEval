Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_long : concatenate_spec ["How"; "much"; "would"; "a"; "chuck"; "a"; "aa"; "woodchuck"; "could"; "wood"] "Howmuchwouldachuckaaawoodchuckcouldwood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.