Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_unicode : concatenate_spec ["The"; "qu🧐ck"; "brown"; "spaces"; "fox"; "jumps"; "the"; "lazy"; "dog"] "Thequ🧐ckbrownspacesfoxjumpsthelazydog".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.