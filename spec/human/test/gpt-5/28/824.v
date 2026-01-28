Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["123"%string; "133"%string; "4566"%string; "456no
newline
this
is
a..
long
string"%string; "10"%string; "11"%string; "12"%string; "13"%string; "144"%string; "15"%string; "1"%string; "17"%string; "1"%string; "123"%string] ("1231334566456no
newline
this
is
a..
long
string10111213144151171123"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.