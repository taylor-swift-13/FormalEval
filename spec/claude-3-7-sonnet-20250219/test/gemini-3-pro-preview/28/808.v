Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["123"; "10"; "11"; "12"; "13"; "14"; "15"; "123"; "16"; "17"; "18"; "11"] "12310111213141512316171811".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.