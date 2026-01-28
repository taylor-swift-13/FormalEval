Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_long_string_list :
  problem_28_spec ["1"; "2"; "3"; "4"; "This"; "6"; "99"; "★"; "strings"; "8"; "555"; ""; "9"; "10"; "list"; "5"; "6"] "1234This699★strings8555910list56".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.