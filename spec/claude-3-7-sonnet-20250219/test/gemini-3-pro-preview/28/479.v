Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["🌞"; "this"; "🧐"; "spcaces"; "🐼🐼"; "🦊"; "🐼characters"] "🌞this🧐spcaces🐼🐼🦊🐼characters".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.