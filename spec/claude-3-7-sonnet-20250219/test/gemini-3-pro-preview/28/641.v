Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["The"; "quick"; "brown"; "xfox"; "8"; "jumps"; "over"; "the"; "lazy"; "dog"] "Thequickbrownxfox8jumpsoverthelazydog".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.