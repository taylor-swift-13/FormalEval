Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_sentence: concatenate_spec ["The"; "quick"; "brown"; "fox"; "8"; "jumps"; "over"; "the"; "lazy"; "dog"] "Thequickbrownfox8jumpsoverthelazydog".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.