Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_unicode: concatenate_spec ["😀"; "🌞"; "this"; "🧐"; "spaces"; "★1"; "★"] "😀🌞this🧐spaces★1★".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.