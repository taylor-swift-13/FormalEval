Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_complex_newlines :
  problem_28_spec
    ["12"; "jum"; "this
string
has
multiple
newlines"; "wooodjum"; "jumps"; "jumps"; "jumps"]
    "12jumthis
string
has
multiple
newlineswooodjumjumpsjumpsjumps".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.