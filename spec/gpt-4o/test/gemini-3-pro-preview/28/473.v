Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec [
"t!!his
string
has
multiple
newlines";
"hello
world";
"thist!!his
string
has
multiple
newlines";
"this
string
has
multiple
newlines";
"hel
world";
"jumps";
"t!!his
string
has
multiple
newlines";
"this
string
has
multiple
newlines"
]
"t!!his
string
has
multiple
newlineshello
worldthist!!his
string
has
multiple
newlinesthis
string
has
multiple
newlineshel
worldjumpst!!his
string
has
multiple
newlinesthis
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.