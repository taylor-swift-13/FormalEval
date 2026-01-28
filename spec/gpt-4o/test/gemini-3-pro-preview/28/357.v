Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec [
"t!!shis
string
has
multiple
newlines"; 
"t!!his
string
has
multiple
newlines"; 
"hello
world"; 
"jumps"; 
"t!!his
string
has
multiple
newlines"; 
"t!!his
string
has
multiple
newlines"; 
"jumps"; 
"hello
world"; 
"t!!his
string
has
multiple
newlines"
] 
"t!!shis
string
has
multiple
newlinest!!his
string
has
multiple
newlineshello
worldjumpst!!his
string
has
multiple
newlinest!!his
string
has
multiple
newlinesjumpshello
worldt!!his
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.