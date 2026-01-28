Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_fox: concatenate_spec ["The"; "quick"; "brown"; "fox"; "jumps"; "over"; "the"; "lazy"; "dog"; "quick"] "Thequickbrownfoxjumpsoverthelazydogquick".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.