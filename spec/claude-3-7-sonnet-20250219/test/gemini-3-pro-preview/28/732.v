Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["456"; "789"; "10"; "11"; "12"; "13"; "17"; "18"; "11"; "123!amuchb"; "11"] "45678910111213171811123!amuchb11".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.