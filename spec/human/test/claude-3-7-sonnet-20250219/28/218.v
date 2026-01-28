Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_complex_multiline :
  problem_28_spec
    ["hello
w555orld"; "this
string
has
multiple
newlines"; "no
newline
this
is

a..
long
string"]
    "hello
w555orldthis
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