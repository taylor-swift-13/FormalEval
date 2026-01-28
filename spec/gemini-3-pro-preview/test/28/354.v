Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_long : concatenate_spec ["The"; "quick"; "woood"; "brown"; "Hellsingleo, World!"; "fox"; "jumps"; "fox"; "extra"; "the"; "lazy"; "over"] "ThequickwooodbrownHellsingleo, World!foxjumpsfoxextrathelazyover".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.