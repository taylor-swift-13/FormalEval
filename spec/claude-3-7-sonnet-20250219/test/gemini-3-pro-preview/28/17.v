Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["1323"; "pythonhello"; "789"] "1323pythonhello789".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.