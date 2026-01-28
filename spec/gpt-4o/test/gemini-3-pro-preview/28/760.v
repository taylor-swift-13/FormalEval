Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long : concatenate_spec ["The"; "quick"; "brown"; "strings"; "fox"; "jumps"; "over"; "the"; "lazy"; "dog"; "the"] "Thequickbrownstringsfoxjumpsoverthelazydogthe".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.