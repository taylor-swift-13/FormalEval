Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec [
"lthis
string
has
multipule
newllHello, W,orld!ines"; "this
string
has
multiple
newlines"; "lthis
string
has
multipule
newlines"; "hello
world"; "this
string
has
mulntiple
newlines"; "this
string
has
mulntiple
newlines"] "lthis
string
has
multipule
newllHello, W,orld!inesthis
string
has
multiple
newlineslthis
string
has
multipule
newlineshello
worldthis
string
has
mulntiple
newlinesthis
string
has
mulntiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.