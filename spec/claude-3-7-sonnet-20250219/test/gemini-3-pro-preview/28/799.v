Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long: concatenate_spec ["The"; "quick"; "brown"; "strings66trsings"; "fox"; "jumps"; "over"; "the"; "lazy"; "dog"] "Thequickbrownstrings66trsingsfoxjumpsoverthelazydog".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.