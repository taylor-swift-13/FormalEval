Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["123"; "45"; "789"; "10"; "11"; "12"; "14"; "15"; "16"; "17"; "or"; "18"; "123"] "1234578910111214151617or18123".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.