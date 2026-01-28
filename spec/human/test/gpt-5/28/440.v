Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["hello
orld"%string; "hello
world"%string; "this
string
has
multiple
newlines"%string; "no
newline
this
is
a..
long
string"%string; "jums"%string; "jumps"%string] ("hello
orldhello
worldthis
string
has
multiple
newlinesno
newline
this
is
a..
long
stringjumsjumps"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.