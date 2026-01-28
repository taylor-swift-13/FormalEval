Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "16"; "456"; "789"; "10"; "11"; "Hello, Woworldrld!"; "12"; "13"; "14"; "15"; "16"; "lazy"; "313"; "18"; "11"; "110"; "15"] "123164567891011Hello, Woworldrld!1213141516lazy313181111015".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.