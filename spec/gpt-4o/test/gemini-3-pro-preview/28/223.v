Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec [
"hello
world"; "this
string
has
multiple
newlines"; "jumps"; "this
string
has
multipule
newlines"; "hellld"; "this
string
has
multiple
newleines"; "hello
world"
]
"hello
worldthis
string
has
multiple
newlinesjumpsthis
string
has
multipule
newlineshellldthis
string
has
multiple
newleineshello
world".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.