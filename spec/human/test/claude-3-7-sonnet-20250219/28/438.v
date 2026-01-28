Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concatenated_strings :
  problem_28_spec ["1"; "2"; "3"; "4"; "5woHwod"; "6"; "7"; "8"; "9"; "10"; "★1"] "12345woHwod678910★1".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.