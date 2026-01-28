Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_full : concatenate_spec ["How"; "much"; "wood"; "would"; "a"; "chuck"; "a"; "aa"; "between"; "could"; "wood"] "Howmuchwoodwouldachuckaaabetweencouldwood".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.