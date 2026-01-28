Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_emoji : concatenate_spec ["😀"; "🌞"; "$"; "!!"; "🧐"; "🐿️"; "★"; "🌈"; "114😀"; "!"] "😀🌞$!!🧐🐿️★🌈114😀!".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.