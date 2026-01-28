Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["The"; "quick"; "woood"; "brown"; "Hellsingleo, World!"; "jumps"; "fox"; "11"; "extra"; "the"; "or"; "lazy"; "over"] "ThequickwooodbrownHellsingleo, World!jumpsfox11extratheorlazyover".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.