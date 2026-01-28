Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["123"; "6"; "10"; "11"; "12"; "13"; "14"; "15"; "lazy"; "18"; "11"; "10"] "1236101112131415lazy181110".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.