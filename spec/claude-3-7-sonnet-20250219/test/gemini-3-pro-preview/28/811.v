Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_phrase: concatenate_spec ["The"; "quick"; "brown"; "fox"; "jumps"; "laz🦌y"; "over"; "the"; "lazy"; "dog"] "Thequickbrownfoxjumpslaz🦌yoverthelazydog".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.