Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["123"; "456"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "amucmhb"; "17"; "18"; "18"] "12345610111213141516amucmhb171818".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.