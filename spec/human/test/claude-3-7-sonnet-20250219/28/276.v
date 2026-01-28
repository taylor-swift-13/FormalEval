Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_string_list :
  problem_28_spec ["1"; "2"; "4"; "without"; "6"; "7"; "8"; "9"; "10"; "★1"; "5"; "6"] "124without678910★156".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.