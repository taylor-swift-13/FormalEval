Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_full : concatenate_spec ["The"; "quick"; "woood"; "brown"; "Hellsingleo, World!"; "jumps"; "fox"; "11"; "extra"; "the"; "lazy"; "over"] "ThequickwooodbrownHellsingleo, World!jumpsfox11extrathelazyover".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.