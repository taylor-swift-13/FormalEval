Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["a"; "abc1amuchb0d"; "amuchb"; "abcd"] "aabc1amuchb0damuchbabcd".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.