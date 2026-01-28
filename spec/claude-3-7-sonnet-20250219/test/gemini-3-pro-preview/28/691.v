Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["amucmhb"; "a"; "!amuchb"; "abcd"] "amucmhba!amuchbabcd".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.