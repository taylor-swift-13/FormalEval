Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["456"; "789"; "10"; "11"; "12"; "13"; "17"; "78"; "11"; "123!amuchb"; "11"; "123!amuchb"] "45678910111213177811123!amuchb11123!amuchb".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.