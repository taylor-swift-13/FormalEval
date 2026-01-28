Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["123"; "456"; "1amuchb0"; "789"; "10"; "11"; "12"; "14"; "16"; "117"; "18"] "1234561amuchb0789101112141611718".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.