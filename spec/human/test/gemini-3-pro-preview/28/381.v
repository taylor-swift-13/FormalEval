Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["The"; "quick"; "woood"; "brown"; "Hellsingleo, World!"; "jumps"; "fox"; "11"; "extra"; "the"; "or"; "lazy"; "over"] "ThequickwooodbrownHellsingleo, World!jumpsfox11extratheorlazyover".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.