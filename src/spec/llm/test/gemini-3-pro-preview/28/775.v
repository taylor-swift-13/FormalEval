Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_long : concatenate_spec ["456"; "789"; "10"; "11"; "12"; "13"; "17"; "78"; "11"; "123!amuchb"; "11"; "123!amuchb"] "45678910111213177811123!amuchb11123!amuchb".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.