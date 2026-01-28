Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["123"; "6"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "18"; "11"; "10"] "1236111213141516lazy181110".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.