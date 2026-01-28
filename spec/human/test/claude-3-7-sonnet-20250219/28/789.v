Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_long_multiline_strings :
  problem_28_spec
    ["hello
world"; "no
newline
this
is
a..
long
string"; "this
string
has
multiple
newlines"; "hello
world"]
    "hello
worldno
newline
this
is
a..
long
stringthis
string
has
multiple
newlineshello
world".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.