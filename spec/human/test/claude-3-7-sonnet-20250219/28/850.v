Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_complex_string :
  problem_28_spec ["313"; "456no"; "this
string
has
multiple
newlines"; "no
newline
this
is
a..
long
string"] "313456nothis
string
has
multiple
newlinesno
newline
this
is
a..
long
string".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.