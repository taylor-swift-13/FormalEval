Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec [
  "313";
  "hello
world";
  "this
string
has
multiple
newlines";
  "no
newline
this
is
a..
long
string"
] "313hello
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
string".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.