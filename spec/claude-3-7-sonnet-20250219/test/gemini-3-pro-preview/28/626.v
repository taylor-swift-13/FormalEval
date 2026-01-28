Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["123"; "456"; "789"; "🦌"; "11"; "12"; "13"; "14"; "15"; "16"; "17"; "18"; "13"] "123456789🦌111213141516171813".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.