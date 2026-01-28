Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_numbers_concatenation :
  problem_28_spec ["1"; "55"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "2"] "15523456789102".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.