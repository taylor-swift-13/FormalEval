Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec ["The"; "qu🧐ck"; "brown"; "spaces"; "fox"; "jumps"; "the"; "lazy"; "dog"] "Thequ🧐ckbrownspacesfoxjumpsthelazydog".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.