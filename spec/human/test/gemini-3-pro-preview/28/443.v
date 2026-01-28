Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec [ "12"; "jumwowoquvSickod"; "multipule"; "jum"; "this
string
has
multiple
newlines"; "wooodjum"; "jumps"; "th6is"; "jumps"; "12" ] "12jumwowoquvSickodmultipulejumthis
string
has
multiple
newlineswooodjumjumpsth6isjumps12".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.