Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec [
  "313"; 
  "456no"; 
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
] 
"313456nothis
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