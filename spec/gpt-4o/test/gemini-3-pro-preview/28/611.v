Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1 : concatenate_spec ["qu🧐ck"; "brown"; "spaces"; "fox"; "jumps"; "the"; "lazy"; "dog"] "qu🧐ckbrownspacesfoxjumpsthelazydog".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.