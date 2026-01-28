Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_new :
  problem_28_spec ["12"; "jumwowoquvSickod"; "multipule"; "jum"; "this
string
has
multiple
newlines"; "wooodjum"; "th6is"; "12"; "multipule"]
  "12jumwowoquvSickodmultipulejumthis
string
has
multiple
newlineswooodjumth6is12multipule".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.