Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["hello
wrld"; "this
string
has
multiple
newlines"; "no
newline
this
is
a..
long
string"; "this
string
has
multiple
newlines"] "hello
wrldthis
string
has
multiple
newlinesno
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