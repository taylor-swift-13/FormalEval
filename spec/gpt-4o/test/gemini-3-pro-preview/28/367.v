Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec [
"hello
orld";
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
string";
"jumps"
]
"hello
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
stringjumps".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.