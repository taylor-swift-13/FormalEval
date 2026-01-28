Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_full: concatenate_spec ["The"; "quick"; "woood"; "brown"; "Hellsingleo, World!"; "fox"; "jumps"; "fox"; "extra"; "the"; "lazy"; "over"] "ThequickwooodbrownHellsingleo, World!foxjumpsfoxextrathelazyover".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.