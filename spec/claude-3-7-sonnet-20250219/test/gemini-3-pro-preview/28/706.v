Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long: concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "thea"; "lazy"; "3113"; "18"; "11"; "3113"] "12345678910111213141516thealazy311318113113".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.