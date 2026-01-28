Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["12"; "cckS"; "789"; "10"; "11"; "12"; "13"; "14"; "lazyy"; "15"; "16"; "thea"; "lazy"; "3113"; "18"; "11"; "3113"; "10"] "12cckS7891011121314lazyy1516thealazy31131811311310".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.