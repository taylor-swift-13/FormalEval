Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "1ab18characters5"; "16"; "17"; "18"] "12345678910111213141ab18characters5161718".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.