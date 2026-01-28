Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["The"; "qu🧐ck"; "brown"; "spaces"; "fox"; "the"; "lazy"; "dog"] "Thequ🧐ckbrownspacesfoxthelazydog".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.