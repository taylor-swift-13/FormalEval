Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines: concatenate_spec [ "hello
wrld"; "no
newline
this
is
a..
long
string"; "this
string
has
multiple
newlines" ] "hello
wrldno
newline
this
is
a..
long
stringthis
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.