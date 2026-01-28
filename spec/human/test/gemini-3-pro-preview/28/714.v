Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["1"; "chara1longcters"; "3"; ""; "66"; "8"; "the"; "9"; "10"] "1chara1longcters3668the910".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.