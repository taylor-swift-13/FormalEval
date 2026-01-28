Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["123"; "456"; "10"; "11"; "13"; "14"; "15"; "16"; "17"; "18"] "1234561011131415161718".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.