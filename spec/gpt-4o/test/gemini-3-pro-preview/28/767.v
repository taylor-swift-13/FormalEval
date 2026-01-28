Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_case1 : concatenate_spec ["😀"; "🌞"; "$"; "🧐"; "🐿️"; "18"; "★"; "🌈"; "!"; "achara1longctersbc8789d"; "🌞"] "😀🌞$🧐🐿️18★🌈!achara1longctersbc8789d🌞".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.