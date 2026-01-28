Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_simple: concatenate_spec ["1323"; "789"; "pythonhello"] "1323789pythonhello".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.