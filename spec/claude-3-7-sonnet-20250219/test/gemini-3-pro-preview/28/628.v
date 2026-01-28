Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines: concatenate_spec [ "313"; "this
string
has
multiple
newlines"; "no
newline
this
is
a..
long
string" ] "313this
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
  reflexivity.
Qed.