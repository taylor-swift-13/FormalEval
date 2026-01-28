Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["456"; "789"; "10"; "11"; "12"; "13"; "17"; "18"; "11"; "123!amuchb"; "11"] "45678910111213171811123!amuchb11".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.