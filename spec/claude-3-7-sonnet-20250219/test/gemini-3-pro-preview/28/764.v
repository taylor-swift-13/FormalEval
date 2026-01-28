Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["no"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; ""; "lazy"; "3113"; "18"; "18"] "no78910111213141516lazy31131818".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.