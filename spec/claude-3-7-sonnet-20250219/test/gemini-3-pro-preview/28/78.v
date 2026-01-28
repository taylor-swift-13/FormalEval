Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["i456banana"; "ppythonhelloythoon"; "a"; "i456banana"] "i456bananappythonhelloythoonai456banana".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.