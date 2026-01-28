Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1 : concatenate_spec ["The"; "quick"; "woood"; "brown"; "Hellsingleo, World!"; "jumps"; "fox"; "11"; "extra"; "the"; "or"; "lazy"; "over"] "ThequickwooodbrownHellsingleo, World!jumpsfox11extratheorlazyover".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.