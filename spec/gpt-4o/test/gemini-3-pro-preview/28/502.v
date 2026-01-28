Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate : concatenate_spec ["🦁"; "🐼"; "🦛"; "multipule"; "🦉"; "🦜"; "🐢"; "wooo🐼charactersd"; "🦌"] "🦁🐼🦛multipule🦉🦜🐢wooo🐼charactersd🦌".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.