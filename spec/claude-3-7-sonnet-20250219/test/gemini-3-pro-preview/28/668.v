Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["789"; "10"; "11"; "12"; "13"; "14"; "15"; "123"; "16"; "17"; "18"] "789101112131415123161718".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.