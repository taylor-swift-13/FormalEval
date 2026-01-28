Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concatenation_of_strings :
  problem_28_spec ["1"; "2"; "3"; "4"; "5"; "6"; "7"; "555"; ""; "9"; "10"; "list"; "5"; "10"; "7"] "1234567555910list5107".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.