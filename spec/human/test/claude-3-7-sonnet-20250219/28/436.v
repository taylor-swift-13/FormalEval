Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_strings_with_newlines :
  problem_28_spec ["12"; "jumwowoquvSickod"; "jum"; "this
string
has
multiple
newlines"; "wooodjum"; "jumps"; "th6is"; "jumps"; "12"; "jum"]
    "12jumwowoquvSickodjumthis
string
has
multiple
newlineswooodjumjumpsth6isjumps12jum".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.