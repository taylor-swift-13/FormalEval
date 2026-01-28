Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec [
"brownthis
string
has
multiple
newlines7789";
"1";
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
"no
newline
this
is
a..
long
string"
]
"brownthis
string
has
multiple
newlines77891hello
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
stringno
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