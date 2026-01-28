Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_unicode: concatenate_spec ["😀"; "🌞"; "$"; "🧐"; "🐿️"; "18"; "★"; "🌈"; "!"; "achara1longctersbc8789d"; "🌞"] "😀🌞$🧐🐿️18★🌈!achara1longctersbc8789d🌞".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.