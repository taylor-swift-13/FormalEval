Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_long_list :
  problem_28_spec ["1"; "2"; "3"; "2🦌"; "4"; "5"; "6"; "7"; "8"; "9"; "e"] "1232🦌456789e".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.