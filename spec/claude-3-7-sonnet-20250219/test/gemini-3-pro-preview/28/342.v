Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec ["The"; "quick"; "woood"; "brown"; "Hellsingleo, World!"; "fox"; "jumps"; "fox"; "11"; "extra"; "the"; "lazy"; "over"] "ThequickwooodbrownHellsingleo, World!foxjumpsfox11extrathelazyover".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.