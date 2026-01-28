Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["a"; "abc1amuchb0d"; "amuchb"; "abcd"] "aabc1amuchb0damuchbabcd".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.