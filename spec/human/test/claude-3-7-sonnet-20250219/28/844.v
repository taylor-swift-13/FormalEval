Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_numbers_and_strings :
  problem_28_spec ["1"; "33"; "2"; "3"; ""; "5"; "66"; "8"; "9"; "3jupmps"; "10"; "2"] "13323566893jupmps102".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.