Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint concatenate (strings : list string) : string :=
  match strings with
  | [] => ""
  | s :: rest => append s (concatenate rest)
  end.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = concatenate strings.

Example test_concatenate_1: concatenate_spec ["The"; "quick"; "woood"; "brown"; "Hellsingleo, World!"; "jumps"; "fox"; "11"; "extra"; "the"; "or"; "lazy"; "over"] "ThequickwooodbrownHellsingleo, World!jumpsfox11extratheorlazyover".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.