Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_newlines : concatenate_spec ["hello
orld"; "hello
world"; "this
string
has
multiple
newlines"; "no
newline
this
is
a..
long
string"; "jums"; "jumps"] "hello
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
stringjumsjumps".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.