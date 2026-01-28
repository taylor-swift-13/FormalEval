Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["The"; "qu🧐ck"; "brown"; "spaces"; "fox"; "jumps"; "lazy"; "dog"; "The"] "Thequ🧐ckbrownspacesfoxjumpslazydogThe".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.