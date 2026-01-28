Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concatenate_string_list :
  problem_28_spec ["1"; "2"; "3"; "4"; "This"; "6"; "★"; "7"; "8"; "555"; ""; "9"; "10"; "list"; "5"] "1234This6★78555910list5".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.