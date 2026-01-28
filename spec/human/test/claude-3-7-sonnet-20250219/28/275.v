Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_long_string_list :
  problem_28_spec ["The"; "quick"; "woood"; "brown"; "Hellsingleo, World!"; "fox"; "jumps"; "fox"; "extra"; "the"; "lazy"; "dog"; "over"]
                   "ThequickwooodbrownHellsingleo, World!foxjumpsfoxextrathelazydogover".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.