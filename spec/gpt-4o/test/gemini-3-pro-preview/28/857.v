Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines : concatenate_spec 
  [ "Hello, World!"; 
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
    "hello
world"; 
    "hello
world" ] 
  "Hello, World!hello
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
stringhello
worldhello
world".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.