Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_string_list :
  problem_28_spec ["string"; "1"; "2"; "3"; "2🦌"; "4"; "5"; "6"; "7"; "1or"; "8"; "9"; "10"] "string1232🦌45671or8910".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.